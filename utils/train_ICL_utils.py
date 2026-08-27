import torch
import torch.nn as nn
import torch.nn.functional as F
import numpy as np
from scipy import integrate
device = torch.device("cuda" if torch.cuda.is_available() else
                      "cpu")
def mylogger(filename, content):
    with open(filename, 'a') as fw:
        print(content, file=fw)

def get_sde_forward(x, t, beta_0, beta_T):
    # out put mean and difssuion coeff
    beta_t = beta_0 + t * (beta_T - beta_0)
    drift = -0.5 * beta_t[:, None, None, None] * x
    discount = 1.0 - torch.exp(-2.0 * beta_0 * t - (beta_T - beta_0) * t ** 2)
    diffusion = torch.sqrt(beta_t * discount)
    return drift, diffusion


def marginal_prob(x, t, beta_0, beta_T, device=device):
    t = torch.tensor(t, device=device)
    #t = t.to(device)
    log_mean_coeff = (-0.25 * t ** 2 * (beta_T - beta_0)
                      - 0.5 * t * beta_0)
    mean = torch.exp(log_mean_coeff)[:, None, None, None] * x
    std = 1.0 - torch.exp(2.0 * log_mean_coeff)
    return mean, std


def get_perturbed_x(x, marginal_prob, t, eps=1e-5):
  random_t = t * torch.ones(x.shape[0], device=x.device) * (1. - eps) + eps
  z = torch.randn_like(x)
  mean, std = marginal_prob(x, random_t)
  perturbed_x = mean + z * std[:, None, None, None]
  return perturbed_x

def loss_score_t(model, x_prompts, x, marginal_prob, eps=1e-5):
  # x_prompts and x should be in the same class
  # x_prompts: [n, Nx, Nx, 1] - prompt images
  # x: [bs, Nx, Nx, 1] - training images
  # perturbed_x: [bs, Nx, Nx, 1] - noisy training images
  # score: [bs, 1, Nx, Nx] - predicted noise (output from model)
  random_t = torch.rand(x.shape[0], device=x.device) * (1. - eps) + eps
  z = torch.randn_like(x)
  mean, std = marginal_prob(x, random_t)
  perturbed_x = mean + z * std[:, None, None, None]
  
  # Model signature: forward(x_t, t, f_set)
  # x_t: noisy image [bs, Nx, Nx, 1]
  # t: timestep [bs]
  # f_set: prompt set [n, Nx, Nx, 1]
  score = model(x_prompts, perturbed_x, random_t)  # [bs, Nx, Nx, 1]
  
  # Convert score to same shape as z for loss calculation
  if score.shape[1] == 1 and z.shape[-1] == 1:
      # score is [bs, 1, Nx, Nx], z is [bs, Nx, Nx, 1]
      score = score.permute(0, 2, 3, 1)  # [bs, Nx, Nx, 1]

  loss = torch.mean(torch.sum((score + z)**2, dim=(1,2,3)))
  return loss


def loss_score_t_prompts(model, x_prompts_list, x, marginal_prob, eps=1e-5):
    """
    x_prompts_list:
      - list of prompt sets, each [N, Nx, Nx, 1], N can vary, len = K
    x: [bs, Nx, Nx, 1]
    """
    bs = x.shape[0]
    device = x.device

    # sample t and noise once (shared across prompt sets)
    random_t = torch.rand(bs, device=device) * (1. - eps) + eps
    z = torch.randn_like(x)

    mean, std = marginal_prob(x, random_t)              # mean: [bs, Nx, Nx, 1], std: [bs] (typical)
    perturbed_x = mean + z * std[:, None, None, None]   # [bs, Nx, Nx, 1]

    per_prompt_losses = []
    for x_prompts in x_prompts_list:
        score = model(x_prompts, perturbed_x, random_t)  # expected [bs, 1, Nx, Nx] or [bs, Nx, Nx, 1]

        # make score shape match z: [bs, Nx, Nx, 1]
        if score.dim() == 4 and score.shape[1] == 1 and z.shape[-1] == 1:
            score = score.permute(0, 2, 3, 1)  # [bs, Nx, Nx, 1]

        per_ex_loss = ((score + z) ** 2).sum(dim=(1, 2, 3))  # [bs]
        per_prompt_losses.append(per_ex_loss)

    per_prompt_losses = torch.stack(per_prompt_losses, dim=0)  # [K, bs]

    return per_prompt_losses.mean()   # mean over K and bs

def loss_score_t_KME(model, KME_list, x, marginal_prob, eps=1e-5):
    """
    KME_list:
      - list of KME embeddings, each [embed,]
    x: [bs, Nx, Nx, 1]
    """
    bs = x.shape[0]
    device = x.device

    # sample t and noise once (shared across prompt sets)
    random_t = torch.rand(bs, device=device) * (1. - eps) + eps
    z = torch.randn_like(x)

    mean, std = marginal_prob(x, random_t)              # mean: [bs, Nx, Nx, 1], std: [bs] (typical)
    perturbed_x = mean + z * std[:, None, None, None]   # [bs, Nx, Nx, 1]

    per_prompt_losses = []
    for x_prompts in KME_list:
        score = model(x_prompts, perturbed_x, random_t)  # expected [bs, 1, Nx, Nx] or [bs, Nx, Nx, 1]

        # make score shape match z: [bs, Nx, Nx, 1]
        if score.dim() == 4 and score.shape[1] == 1 and z.shape[-1] == 1:
            score = score.permute(0, 2, 3, 1)  # [bs, Nx, Nx, 1]

        per_ex_loss = ((score + z) ** 2).sum(dim=(1, 2, 3))  # [bs]
        per_prompt_losses.append(per_ex_loss)

    per_prompt_losses = torch.stack(per_prompt_losses, dim=0)  # [K, bs]

    return per_prompt_losses.mean()   # mean over K and bs



def Euler_Maruyama_sampler(score_model,
               marginal_prob,
               get_sde_forward,
               init_x,
               x_prompts,
               num_steps=500,
               device=device,
               eps=1e-3,
               T=1):
    batch_size = init_x.shape[0]
    time_steps = torch.linspace(T, eps, num_steps, device=device)
    dt = (eps - T) / num_steps  # negative

    x = init_x.clone().to(device)
    x_prompts = x_prompts.to(device)

    with torch.no_grad():
        for step_idx, t in enumerate(time_steps):
            t_batch = torch.ones(batch_size, device=device) * t

            score = score_model(x_prompts, x, t_batch)   # scaled score
            drift, g = get_sde_forward(x, t_batch)
            _, std = marginal_prob(x, t_batch)

            drift_corr = -(g**2)[:, None, None, None] / (std[:, None, None, None] + 1e-12) * score
            total_drift = drift + drift_corr

            noise = torch.randn_like(x)
            x = x + total_drift * dt + g[:, None, None, None] * torch.sqrt(torch.tensor(-dt, device=device)) * noise

    return x


########### this is previous version #############

def em_sampler(score_model,
               marginal_prob,
               get_sde_forward,
               init_x,
               x_prompts,
               num_steps=500,
               device=device,
               eps=1e-3,
               T=1):
    """
    Euler–Maruyama sampler for reverse-time SDE with GLOBAL PROMPTS.

    Args:
        score_model: model(x, t, f_prompts)
        marginal_prob: returns (mean, std) of x_t | x_0
        get_sde_forward: forward SDE drift + diffusion coefficient g(t)
        init_x: initial noise, shape [B, 1, Nx, Nx]
        x_prompts: prompt set, shape [N, 1, Nx, Nx] or [N, Nx, Nx, 1]
        num_steps: number of steps
        eps: minimum time
        T: maximum time
    """
    batch_size = init_x.shape[0]
    time_steps = torch.linspace(T, eps, num_steps, device=device)
    dt = (eps - T) / num_steps
    
    x = init_x.clone().to(device)
    x_prompts = x_prompts.to(device)

    with torch.no_grad():
        for step_idx, t in enumerate(time_steps):
            # SAME TIME FOR ENTIRE BATCH
            t_batch = torch.ones(batch_size, device=device) * t

            # -------------------------------------------
            # SCORE MODEL WITH PROMPTS!!!!
            # -------------------------------------------
            score = score_model(x_prompts, x, t_batch)

            # Drift and diffusion from forward VP/VE SDE
            drift, g = get_sde_forward(x, t_batch)

            # Compute std of x_t (used in reverse SDE drift correction)
            _, std = marginal_prob(x, t_batch)

            # Reverse-SDE correction term:
            #    drift_correction = -½ * g(t)^2 / std * score
            drift_corr = -0.5 * (g**2)[:, None, None, None] / std[:, None, None, None] * score

            # Total drift term
            total_drift = drift + drift_corr

            # Euler–Maruyama update
            x = x + total_drift * dt

            # Logging
            if (step_idx + 1) % 100 == 0 or step_idx == 0:
                print(f"[{step_idx+1}/{num_steps}] t={t.item():.4f}")

    return x


def ode_solver(score_model,
                marginal_prob,
                get_sde_forward,
                init_x,
                x_prompts,
                forward,
                atol=1e-6,
                rtol=1e-6,
                device=device,
                eps=1e-3,
                T=1,
                method='RK45',
                use_euler=False,
                use_em=False,
                num_steps=500):
    """
    ODE solver for sampling with GLOBAL PROMPTS.
    Supports:
        • Euler–Maruyama sampler (use_em=True)
        • SciPy ODE solver (reverse-time probability flow ODE)
    """

    # ============================================================
    #  FAST SAMPLER (EM)
    # ============================================================
    if use_euler:
        print(f"Using Euler-Maruyama sampler with {num_steps} steps")
        return em_sampler(score_model, marginal_prob, get_sde_forward,
                          init_x, x_prompts,
                          num_steps=num_steps, device=device, eps=eps, T=T)
    
    # ============================================================
    #  FAST SAMPLER (EM)
    # ============================================================
    if use_em:
        print(f"Using Euler-Maruyama sampler with {num_steps} steps")
        return Euler_Maruyama_sampler(score_model, marginal_prob, get_sde_forward,
                          init_x, x_prompts,
                          num_steps=num_steps, device=device, eps=eps, T=T)

    # ============================================================
    #  SLOW SAMPLER (SciPy ODE Solver)
    # ============================================================

    shape = init_x.shape
    x_prompts = x_prompts.to(device)

    # -----------------------------
    # Score wrapper WITH PROMPTS
    # -----------------------------
    def score_eval_wrapper(sample, time_steps):
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((shape[0],))
        with torch.no_grad():
            score = score_model(x_prompts, sample, time_steps)
        return score.cpu().numpy().reshape((-1,)).astype(np.float64)

    # -----------------------------
    # SDE forward drift wrapper
    # -----------------------------
    def get_sde_forward_eval_wrapper(sample, time_steps):
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((shape[0],))
        with torch.no_grad():
            drift, g = get_sde_forward(sample, time_steps)
        return (drift.cpu().numpy().reshape((-1,)).astype(np.float64),
                g.cpu().numpy().reshape((-1,)).astype(np.float64))

    # -----------------------------
    # Marginal prob wrapper
    # -----------------------------
    def marginal_prob_eval_wrapper(sample, time_steps):
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((shape[0],))
        with torch.no_grad():
            mean, std = marginal_prob(sample, time_steps)
        return (mean.cpu().numpy().reshape((-1,)).astype(np.float64),
                std.cpu().numpy())

    # -----------------------------
    # ODE function
    # dx/dt = drift - ½ g^2 / std * score
    # -----------------------------
    def ode_func(t, x_flat):
        time_steps = np.ones((shape[0],)) * t

        drift, g = get_sde_forward_eval_wrapper(x_flat, time_steps)
        mean, std = marginal_prob_eval_wrapper(x_flat, time_steps)

        score = score_eval_wrapper(x_flat, time_steps)

        return drift - 0.5 * (g[0] ** 2) / std[0] * score

    # -----------------------------
    # Run ODE Solver
    # -----------------------------
    print(f"Using scipy ODE solver with method={method}")

    if forward == 1:
        res = integrate.solve_ivp(
            ode_func, (eps, T), init_x.reshape(-1).cpu().numpy(),
            rtol=rtol, atol=atol, method=method
        )
    else:
        res = integrate.solve_ivp(
            ode_func, (T, eps), init_x.reshape(-1).cpu().numpy(),
            rtol=rtol, atol=atol, method=method
        )

    print(f"Number of function evaluations: {res.nfev}")

    x = torch.tensor(res.y[:, -1], device=device, dtype=torch.float32).reshape(shape)
    return x
