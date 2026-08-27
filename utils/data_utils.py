import numpy as np
import jax
import jax.numpy as jnp
import jax_cfd.base as cfd
import numpy as np
import seaborn
import xarray
import matplotlib.pyplot as plt


def generate_ns_image(N=1000, size=128, nu_range=(2e-3, 8e-2), seed=1):
    """
    nu_range: scalar, single (low, high) tuple, or two sub-ranges
              ((low1, high1), (low2, high2)) sampled with equal probability.
    seed: base random seed; each trajectory i uses PRNGKey(seed + i).
    """
    np.random.seed(seed)
    if isinstance(nu_range, (int, float)):
        nu = float(nu_range)
    elif isinstance(nu_range[0], (tuple, list)):
        if np.random.rand() < 0.5:
            nu = np.random.uniform(*nu_range[0])
        else:
            nu = np.random.uniform(*nu_range[1])
    else:
        nu = np.random.uniform(*nu_range)
    density = 1.
    inner_steps = 30
    outer_steps = 20

    max_velocity = 2.0
    cfl_safety_factor = 0.2
    
    # Define the physical dimensions of the simulation.
    grid = cfd.grids.Grid((size, size), domain=((0, 2 * jnp.pi), (0, 2 * jnp.pi)))
    
    # Choose a time step.
    dt = cfd.equations.stable_time_step(
        max_velocity, cfl_safety_factor, nu, grid)
    
    # Define a step function
    step_fn = cfd.funcutils.repeated(
        cfd.equations.semi_implicit_navier_stokes(
            density=density, viscosity=nu, dt=dt, grid=grid),
        steps=inner_steps)
    rollout_fn = jax.jit(cfd.funcutils.trajectory(step_fn, outer_steps))
    
    # Initialize array to store vorticity of last snapshots
    vorticity_data = np.zeros((N, size, size))
    
    # Generate N trajectories
    for i in range(N):
        # Use different seed for each trajectory
        v0 = cfd.initial_conditions.filtered_velocity_field(
            jax.random.PRNGKey(seed + i), grid, max_velocity)
        
        # Run simulation and get trajectory
        _, trajectory = jax.device_get(rollout_fn(v0))
        
        # Create xarray Dataset from trajectory
        ds = xarray.Dataset(
            {
                'u': (('time', 'x', 'y'), trajectory[0].data),
                'v': (('time', 'x', 'y'), trajectory[1].data),
            },
            coords={
                'x': grid.axes()[0],
                'y': grid.axes()[1],
                'time': dt * inner_steps * np.arange(outer_steps)
            }
        )
        
        # Compute vorticity: dv/dx - du/dy
        vorticity = ds.v.differentiate('x') - ds.u.differentiate('y')
        
        # Save only the last snapshot (index -1)
        vorticity_data[i] = vorticity.data[-1]
        
        if (i + 1) % 100 == 0:
            print(f"Generated {i + 1}/{N} trajectories")
    
    return vorticity_data

def gaussian_image(mean, Sigma, img_size=32):
    """
    Generate a 2D Gaussian bump on [0,1]^2 with values normalized to [0,1].

    Args:
        mean: (2,) array-like, center (mx, my)
        Sigma: (2,2) covariance matrix
        img_size: resolution (default=32)

    Returns:
        img: (img_size, img_size) numpy array, normalized to [0,1]
    """

    mean = np.array(mean).reshape(2,)
    Sigma = np.array(Sigma).reshape(2, 2)

    # Build grid in [0,1]
    x = np.linspace(0, 1, img_size)
    y = np.linspace(0, 1, img_size)
    x_grid, y_grid = np.meshgrid(x, y)

    # Gaussian evaluation
    invSigma = np.linalg.inv(Sigma)
    coords = np.stack([x_grid, y_grid], axis=-1)
    diff = coords - mean
    md2 = np.einsum('...i,ij,...j->...', diff, invSigma, diff)

    img = np.exp(-0.5 * md2)

    # Normalize to [0,1]
    img = img - img.min()
    img = img / (img.max() + 1e-12)

    return img

def sample_covariance_full(
    sx_range=(0.03, 0.15),
    sy_range=(0.03, 0.15),
    rho_range=(-0.5, 0.5)
):
    """
    Sample a 2x2 positive definite covariance matrix with:
      - different scales in x and y
      - random correlation (rotation/tilt)

    Returns:
        Sigma: (2,2) numpy array
    """
    sx = np.random.uniform(*sx_range)   # std in x
    sy = np.random.uniform(*sy_range)   # std in y
    rho = np.random.uniform(*rho_range) # correlation, keeps PD if |rho| < 1

    Sigma = np.array([
        [sx * sx,      rho * sx * sy],
        [rho * sx * sy, sy * sy     ]
    ])
    return Sigma

def gen_dataset_one(N, seed = 1):
    np.random.seed(seed)
    if np.random.rand() < 0.5:
        mean_x = np.random.uniform(0.2, 0.48)
    else:
        mean_x = np.random.uniform(0.52, 0.8)

    if np.random.rand() < 0.5:
        mean_y = np.random.uniform(0.2, 0.48)
    else:
        mean_y = np.random.uniform(0.52, 0.8)
    mean_x = float(round(mean_x, 3))
    mean_y = float(round(mean_y, 3))

    imgs = []
    sigmas = []
    mean = [mean_x, mean_y]

    for _ in range(N):
        Sigma = sample_covariance_full()
        img = gaussian_image(mean, Sigma)
        imgs.append(img)
        sigmas.append(Sigma)

    # Convert to numpy array and save
    imgs_array = np.array(imgs)
    return imgs_array





def grf_laplacian_2d_batch(
    B,
    N,
    L=1.0,
    alpha=1.0,
    beta=1.0,
    sigma=1.0,
    seed=None,
):
    """
    Sample B Gaussian random fields in 2D with covariance ~ (-Δ + β I)^(-α)
    on a periodic domain [0, L]^2 using spectral synthesis.

    Returns:
        u : array of shape (B, N, N)
    """
    if seed is not None:
        np.random.seed(seed)

    # ---- Fourier frequencies ----
    kx = 2 * np.pi * np.fft.fftfreq(N, d=L / N).reshape(-1, 1)
    ky = 2 * np.pi * np.fft.fftfreq(N, d=L / N).reshape(1, -1)
    k2 = kx**2 + ky**2

    # power spectrum S(k) = sigma^2 (|k|^2 + beta)^(-alpha)
    if beta == 0.0:
        k2[0, 0] = np.inf   # avoid singularity at k=0

    lam = (k2 + beta)**(-alpha)
    S = sigma**2 * lam               # shape (N, N)

    # ---- sample complex white noise for each batch ----
    # noise_real, noise_imag: (B, N, N)
    noise_real = np.random.randn(B, N, N)
    noise_imag = np.random.randn(B, N, N)
    W = noise_real + 1j * noise_imag

    # ---- multiply sqrt spectrum ----
    # U_hat: (B, N, N)
    U_hat = W * np.sqrt(S)[None, :, :]

    # ---- inverse FFT for each batch ----
    u = np.fft.ifft2(U_hat, axes=(1,2)).real  # (B, N, N)

    return u


def gen_GRF_dataset_one(B, N, seed=1, alpha_range=((1.2, 2.0), (2.2, 3.0))):
    """
    alpha_range: either a single tuple (low, high) to sample alpha uniformly,
                 or a tuple of two tuples ((low1, high1), (low2, high2)) to
                 sample from two sub-ranges with equal probability.
    """
    np.random.seed(seed)
    # Sample alpha from the provided range(s)
    if isinstance(alpha_range, (int, float)):
        alpha = alpha_range
    elif isinstance(alpha_range[0], (tuple, list)):
        if np.random.rand() < 0.5:
            alpha = np.random.uniform(*alpha_range[0])
        else:
            alpha = np.random.uniform(*alpha_range[1])
    else:
        alpha = np.random.uniform(*alpha_range)

    beta = np.random.uniform(2.0, 2.0)
    imgs = grf_laplacian_2d_batch(B=B, N=N, alpha=alpha, beta=beta)
    return imgs





#### ood data generation ####
def gen_dataset_one_ood(N, seed = 1):
    np.random.seed(seed)

    mean_x = np.random.uniform(0.48, 0.52)
    mean_y = np.random.uniform(0.48, 0.52)

    mean_x = float(round(mean_x, 3))
    mean_y = float(round(mean_y, 3))

    imgs = []
    sigmas = []
    mean = [mean_x, mean_y]

    for _ in range(N):
        Sigma = sample_covariance_full()
        img = gaussian_image(mean, Sigma)
        imgs.append(img)
        sigmas.append(Sigma)

    # Convert to numpy array and save
    imgs_array = np.array(imgs)
    return imgs_array

def gen_dataset_one_ood_fix(N, mean_x=0.5, mean_y=0.5, seed = 1):
    np.random.seed(seed)

    imgs = []
    sigmas = []
    mean = [mean_x, mean_y]

    for _ in range(N):
        Sigma = sample_covariance_full()
        img = gaussian_image(mean, Sigma)
        imgs.append(img)
        sigmas.append(Sigma)

    # Convert to numpy array and save
    imgs_array = np.array(imgs)
    return imgs_array