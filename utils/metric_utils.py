import numpy as np
from scipy.stats import gaussian_kde


def _flatten_images(x: np.ndarray) -> np.ndarray:
    """Flatten [N, Nx, Nx] or [N, Nx, Nx, 1] -> [N, D] as float64."""
    x = np.asarray(x)
    if x.ndim == 3:
        return x.reshape(x.shape[0], -1).astype(np.float64, copy=False)
    elif x.ndim == 4 and x.shape[-1] == 1:
        return x.reshape(x.shape[0], -1).astype(np.float64, copy=False)
    else:
        raise ValueError(f"Expected shape [N,Nx,Nx] or [N,Nx,Nx,1], got {x.shape}")


def _rbf_kernel_matrix(x: np.ndarray, y: np.ndarray, sigma: float) -> np.ndarray:
    """Compute RBF kernel matrix exp(-||x-y||^2/(2*sigma^2))."""
    if sigma <= 0:
        raise ValueError("sigma must be > 0")

    # ||x-y||^2 = ||x||^2 + ||y||^2 - 2 x y^T
    x2 = np.sum(x * x, axis=1, keepdims=True)  # (N,1)
    y2 = np.sum(y * y, axis=1, keepdims=True).T  # (1,M)
    d2 = x2 + y2 - 2.0 * (x @ y.T)
    d2 = np.maximum(d2, 0.0)
    return np.exp(-d2 / (2.0 * sigma * sigma))


def mmd2_rbf(x: np.ndarray, y: np.ndarray, sigma: float = 1.0, unbiased: bool = True) -> float:
    """Compute MMD^2 between two empirical sets using an RBF kernel.

    Args:
        x: array [N, Nx, Nx, 1]
        y: array [M, Nx, Nx, 1]
        sigma: RBF bandwidth
        unbiased: if True, use unbiased U-statistic estimator

    Returns:
        mmd2: scalar float
    """
    x = _flatten_images(x)
    y = _flatten_images(y)

    n = x.shape[0]
    m = y.shape[0]
    if n < 2 and unbiased:
        raise ValueError("Need N>=2 for unbiased estimator")
    if m < 2 and unbiased:
        raise ValueError("Need M>=2 for unbiased estimator")

    k_xx = _rbf_kernel_matrix(x, x, sigma)
    k_yy = _rbf_kernel_matrix(y, y, sigma)
    k_xy = _rbf_kernel_matrix(x, y, sigma)

    if unbiased:
        # remove diagonal terms
        sum_xx = (np.sum(k_xx) - np.trace(k_xx)) / (n * (n - 1))
        sum_yy = (np.sum(k_yy) - np.trace(k_yy)) / (m * (m - 1))
    else:
        sum_xx = np.mean(k_xx)
        sum_yy = np.mean(k_yy)

    sum_xy = np.mean(k_xy)
    return float(sum_xx + sum_yy - 2.0 * sum_xy)


def mmd_rbf(x: np.ndarray, y: np.ndarray, l: float = 0.01) -> float:
    """Compute (biased) MMD with Gaussian kernel k(u,v)=exp(-||u-v||^2/(2 l^2)).

    Matches the formula shown in the screenshot (includes diagonal terms).

    Args:
        x: [N, Nx, Nx, 1]
        y: [M, Nx, Nx, 1]
        l: kernel length-scale (bandwidth)

    Returns:
        mmd: float
    """
    x = _flatten_images(x)
    y = _flatten_images(y)

    k_xx = _rbf_kernel_matrix(x, x, l)
    k_yy = _rbf_kernel_matrix(y, y, l)
    k_xy = _rbf_kernel_matrix(x, y, l)

    return float(np.mean(k_xx) + np.mean(k_yy) - 2.0 * np.mean(k_xy))


def w2_pot(x: np.ndarray, y: np.ndarray) -> float:
    """Compute Wasserstein-2 distance between two empirical sets using POT.

    This implements the discrete OT distance with uniform weights and returns:
        W2 = sqrt( min_pi sum_{i,j} pi_{ij} ||x_i - y_j||_2^2 )

    Args:
        x: [N, Nx, Nx, 1]
        y: [M, Nx, Nx, 1]

    Returns:
        w2: float

    Notes:
        Requires `pip install pot` (package name: POT, import as `ot`).
    """
    try:
        import ot  # type: ignore
    except Exception as e:  # pragma: no cover
        raise ImportError("w2_pot requires POT: `pip install pot`") from e

    x = _flatten_images(x)
    y = _flatten_images(y)
    n = x.shape[0]
    m = y.shape[0]

    a = np.full(n, 1.0 / n, dtype=np.float64)
    b = np.full(m, 1.0 / m, dtype=np.float64)

    # squared Euclidean cost matrix
    x2 = np.sum(x * x, axis=1, keepdims=True)
    y2 = np.sum(y * y, axis=1, keepdims=True).T
    C = x2 + y2 - 2.0 * (x @ y.T)
    C = np.maximum(C, 0.0)

    w2_sq = ot.emd2(a, b, C)  # returns min <pi, C>
    return float(np.sqrt(w2_sq))


import numpy as np
def radial_energy_spectrum_batch(arr, num_modes=36):
    """
    Compute isotropic/radially averaged energy spectrum for a batch of 2D fields,
    truncated to the first `num_modes` radial modes.

    Parameters
    ----------
    arr : np.ndarray
        Shape [B, Nx, Nx] or [B, Nx, Nx, 1].
    num_modes : int
        Number of radial modes to keep.

    Returns
    -------
    E : np.ndarray
        Shape [B, num_modes], where
        E[b, k] is the shell-summed energy spectrum of sample b at radius k.
    """
    arr = np.asarray(arr)
    if arr.ndim == 4:
        assert arr.shape[-1] == 1
        arr = arr[..., 0]
    assert arr.ndim == 3
    B, Nx, Ny = arr.shape
    assert Nx == Ny, "Only square images supported."

    F = np.fft.fftn(arr, axes=(-2, -1))
    power = np.abs(F) ** 2

    kx = np.fft.fftfreq(Nx) * Nx
    ky = np.fft.fftfreq(Ny) * Ny
    KX, KY = np.meshgrid(kx, ky, indexing="ij")
    kr = np.sqrt(KX**2 + KY**2)
    kr_bin = np.rint(kr).astype(np.int64)

    E = np.zeros((B, num_modes), dtype=np.float64)
    flat_bins = kr_bin.ravel()
    valid = flat_bins < num_modes

    for b in range(B):
        E[b] = np.bincount(
            flat_bins[valid],
            weights=power[b].ravel()[valid],
            minlength=num_modes
        )[:num_modes]

    return E


def melr(x, y, weights="uniform", num_modes=36, eps=1e-12, return_spectra=False):
    """
    Compute truncated MELR between two empirical datasets x and y.

    Parameters
    ----------
    x : np.ndarray
        Shape [N, Nx, Nx, 1] or [N, Nx, Nx]
    y : np.ndarray
        Shape [M, Nx, Nx, 1] or [M, Nx, Nx]
    weights : str or np.ndarray
        - "uniform": w_k = 1 / num_modes
        - "weighted": w_k = E_v(k) / sum_q E_v(q)
        - array of shape [num_modes]: custom weights, will be normalized
    num_modes : int
        Truncate to the first `num_modes` radial modes.
    eps : float
        Small constant for numerical stability in log.
    return_spectra : bool
        If True, also return Ex and Ey.

    Returns
    -------
    score : float
        MELR(x, y)
    Ex : np.ndarray, optional
        Average spectrum of x
    Ey : np.ndarray, optional
        Average spectrum of y
    """
    Ex_batch = radial_energy_spectrum_batch(x, num_modes=num_modes)
    Ey_batch = radial_energy_spectrum_batch(y, num_modes=num_modes)

    Ex = Ex_batch.mean(axis=0)   # E_u(k)
    Ey = Ey_batch.mean(axis=0)   # E_v(k)

    if weights == "uniform":
        w = np.ones_like(Ex, dtype=np.float64) / len(Ex)
    elif weights == "weighted":
        w = Ey / (Ey.sum() + eps)
    else:
        w = np.asarray(weights, dtype=np.float64)
        if w.shape != Ex.shape:
            raise ValueError(f"weights must have shape {Ex.shape}, got {w.shape}")
        w = w / (w.sum() + eps)

    score = np.sum(w * np.abs(np.log((Ex + eps) / (Ey + eps))))

    if return_spectra:
        return score, Ex, Ey
    return score



def pdf_kde(
    data,
    label="dataset",
    num_points=400,
    bw_method="scott"
):
    """
    Plot KDE-estimated PDF of scalar values from an empirical dataset.

    Parameters
    ----------
    data : np.ndarray
        Array of shape [N, Nx, Nx, 1] or [N, Nx, Nx].
    label : str
        Label for the plotted curve.
    num_points : int
        Number of points in the evaluation grid.
    bw_method : str, scalar, or callable
        Bandwidth method for scipy.stats.gaussian_kde.
        Examples: None, 'scott', 'silverman', 0.2, etc.

    Returns
    -------
    pdf : np.ndarray
        Estimated PDF values on the grid.
    """
    data = np.asarray(data)

    if data.ndim == 4:
        if data.shape[-1] != 1:
            raise ValueError(f"Expected last channel = 1, got shape {data.shape}")
        vals = data[..., 0].reshape(-1)
    elif data.ndim == 3:
        vals = data.reshape(-1)
    else:
        raise ValueError(f"Expected shape [N,Nx,Nx,1] or [N,Nx,Nx], got {data.shape}")

    vals = vals[np.isfinite(vals)]
    if len(vals) < 2:
        raise ValueError("Need at least two finite values for KDE.")

    kde = gaussian_kde(vals, bw_method=bw_method)

    grid = np.linspace(-1, 1, num_points)
    pdf = kde(grid)

    return grid, pdf

def jsd_kde(sample_data, ref_data, num_points=400, bw_method="scott", eps=1e-12):
    """
    Compute Jensen-Shannon Divergence between two empirical datasets using KDE-estimated PDFs.

    Parameters
    ----------
    sample_data : np.ndarray
        Shape [N, Nx, Nx, 1] or [N, Nx, Nx].
    ref_data : np.ndarray
        Shape [M, Nx, Nx, 1] or [M, Nx, Nx].
    num_points : int
        Number of points in the evaluation grid for KDE.
    bw_method : str, scalar, or callable
        Bandwidth method for scipy.stats.gaussian_kde.
    eps : float
        Small constant for numerical stability in log.

    Returns
    -------
    jsd : float
        Estimated Jensen-Shannon Divergence between the two datasets.
    """
    grid, pdf_sample = pdf_kde(sample_data, num_points=num_points, bw_method=bw_method)
    _, pdf_ref = pdf_kde(ref_data, num_points=num_points, bw_method=bw_method)

    pdf_sample = pdf_sample / (pdf_sample.sum() + eps)
    pdf_ref = pdf_ref / (pdf_ref.sum() + eps)

    m = 0.5 * (pdf_sample + pdf_ref)

    kl_sample_m = np.sum(pdf_sample * np.log((pdf_sample + eps) / (m + eps)))
    kl_ref_m = np.sum(pdf_ref * np.log((pdf_ref + eps) / (m + eps)))

    jsd = 0.5 * (kl_sample_m + kl_ref_m)
    return jsd