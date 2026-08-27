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

def loss_score_t(model, x, marginal_prob, eps=1e-5):
  random_t = torch.rand(x.shape[0], device=x.device) * (1. - eps) + eps
  z = torch.randn_like(x)
  mean, std = marginal_prob(x, random_t)
  perturbed_x = mean + z * std[:, None, None, None]
  score = model(perturbed_x, random_t)

  loss = torch.mean(torch.sum((score + z)**2, dim=(1,2,3)))
  return loss


def em_sampler(score_model,
               marginal_prob,
               get_sde_forward,
               init_x,
               num_steps=500,
               device=device,
               eps=1e-3,
               T=1):
    """
    Euler-Maruyama sampler for reverse-time SDE.
    Much faster than ODE solver for generation.
    
    Args:
        score_model: The trained score model
        marginal_prob: Function to compute marginal probability
        get_sde_forward: Function to compute SDE drift and diffusion
        init_x: Initial noise tensor
        num_steps: Number of discretization steps (default: 500)
        device: Device to run on
        eps: Minimum time (default: 1e-3)
        T: Maximum time (default: 1)
    """
    batch_size = init_x.shape[0]
    time_steps = torch.linspace(T, eps, num_steps, device=device)
    dt = (eps - T) / num_steps
    
    x = init_x.clone()
    
    with torch.no_grad():
        for i, t in enumerate(time_steps):
            # Current time for all samples in batch
            t_batch = torch.ones(batch_size, device=device) * t
            
            # Get score from model
            score = score_model(x, t_batch)
            
            # Get drift and diffusion coefficients
            drift, g = get_sde_forward(x, t_batch)
            
            # Get marginal probability std
            _, std = marginal_prob(x, t_batch)
            
            # Compute drift correction term (reverse-time SDE)
            drift_correction = -0.5 * (g ** 2)[:, None, None, None] / std[:, None, None, None] * score
            
            # Total drift
            total_drift = drift + drift_correction
            
            # Euler-Maruyama step
            x = x + total_drift * dt
            
            # Optional: print progress
            if (i + 1) % 100 == 0 or i == 0:
                print(f"Sampling step {i+1}/{num_steps}, time: {t:.4f}")
    
    return x


def ode_solver(score_model,
                marginal_prob,
                get_sde_forward,
                init_x,
                forward,
                atol=1e-6,
                rtol=1e-6,
                device=device,
                eps=1e-3,
                T=1,
                method='RK45',
                use_em=False,
                num_steps=500):
    """
    ODE solver for sampling. Can use either scipy ODE solver or fast EM method.
    
    Args:
        use_em: If True, use Euler-Maruyama method (much faster). If False, use scipy ODE solver.
        num_steps: Number of steps for EM method (only used if use_em=True)
        method: ODE solver method (only used if use_em=False), e.g., 'RK45', 'Euler'
    """
    # Use fast EM sampler if requested
    if use_em:
        print(f"Using Euler-Maruyama sampler with {num_steps} steps")
        return em_sampler(score_model, marginal_prob, get_sde_forward, init_x, 
                         num_steps=num_steps, device=device, eps=eps, T=T)
    
    # Original ODE solver code
    shape = init_x.shape

    def score_eval_wrapper(sample, time_steps):
        """A wrapper of the score-based model for use by the ODE solver."""
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((sample.shape[0],))
        with torch.no_grad():
            score = score_model(sample, time_steps)
        return score.cpu().numpy().reshape((-1,)).astype(np.float64)

    def get_sde_forward_eval_wrapper(sample, time_steps):
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((sample.shape[0],))
        with torch.no_grad():
            drfit, g = get_sde_forward(sample, time_steps)
        return drfit.cpu().numpy().reshape((-1,)).astype(np.float64), g.cpu().numpy().reshape((-1,)).astype(np.float64)

    def marginal_prob_eval_wrapper(sample, time_steps):
        sample = torch.tensor(sample, device=device, dtype=torch.float32).reshape(shape)
        time_steps = torch.tensor(time_steps, device=device, dtype=torch.float32).reshape((sample.shape[0],))
        with torch.no_grad():
            mean, std = marginal_prob(sample, time_steps)
        return mean.cpu().numpy().reshape((-1,)).astype(np.float64), std.cpu().numpy()

    def ode_func(t, x):
        """The ODE function for use by the ODE solver."""
        time_steps = np.ones((shape[0],)) * t

        drift, g =get_sde_forward_eval_wrapper(x, time_steps)
        mean, std = marginal_prob_eval_wrapper(x, time_steps)

        return drift - 0.5 * (g[0] ** 2) / std[0] * score_eval_wrapper(x, time_steps)

    # Run the black-box ODE solver.
    print(f"Using scipy ODE solver with method={method}")
    if forward ==1:
        # forward
        res = integrate.solve_ivp(ode_func, (eps, T), init_x.reshape(-1).cpu().numpy(), rtol=rtol, atol=atol, method=method)
    else:
        res = integrate.solve_ivp(ode_func, (T, eps), init_x.reshape(-1).cpu().numpy(), rtol=rtol, atol=atol, method=method)
    print(f"Number of function evaluations: {res.nfev}")
    x = torch.tensor(res.y[:, -1], device=device, dtype=torch.float32).reshape(shape)

    return x