import torch
from typing import Optional, Dict, Any


def _flatten_distributions(
    x: torch.Tensor,
    *,
    single_distribution: Optional[bool] = None,
) -> torch.Tensor:
    """
    x:
        - [M, N, H, W]     -> returns [M, N, D]
        - [M, N, H, W, C]  -> returns [M, N, D]
        - [B, n, H, W]     -> returns [B, n, D]
        - [B, n, H, W, C]  -> returns [B, n, D]
        - [n, H, W]        -> returns [1, n, D]
        - [n, H, W, C]     -> returns [1, n, D]

    Notes:
        - 4D inputs are ambiguous between [B, n, H, W] and [n, H, W, C].
        - If `single_distribution` is None, a last dimension of 1 or 3 is
          treated as a channel dimension and interpreted as [n, H, W, C].
        - Pass `single_distribution=False` to force [B, n, H, W].
        - Pass `single_distribution=True` to force [n, H, W, C].
    """
    if x.ndim == 5:
        if x.shape[0] == 0:
            raise ValueError("Input must contain at least one distribution.")
        if x.shape[1] == 0:
            raise ValueError("Each distribution must contain at least one sample.")
        return x.reshape(x.shape[0], x.shape[1], -1).to(torch.float32)
    elif x.ndim == 4:
        if single_distribution is True:
            if x.shape[0] == 0:
                raise ValueError("Input must contain at least one sample.")
            return x.reshape(1, x.shape[0], -1).to(torch.float32)
        if single_distribution is False:
            if x.shape[0] == 0:
                raise ValueError("Input must contain at least one distribution.")
            if x.shape[1] == 0:
                raise ValueError("Each distribution must contain at least one sample.")
            return x.reshape(x.shape[0], x.shape[1], -1).to(torch.float32)
        if x.shape[-1] in (1, 3):
            if x.shape[0] == 0:
                raise ValueError("Input must contain at least one sample.")
            return x.reshape(1, x.shape[0], -1).to(torch.float32)
        if x.shape[0] == 0:
            raise ValueError("Input must contain at least one distribution.")
        if x.shape[1] == 0:
            raise ValueError("Each distribution must contain at least one sample.")
        return x.reshape(x.shape[0], x.shape[1], -1).to(torch.float32)
    elif x.ndim == 3:
        if x.shape[0] == 0:
            raise ValueError("Input must contain at least one sample.")
        return x.reshape(1, x.shape[0], -1).to(torch.float32)
    else:
        raise ValueError(
            f"Expected x.ndim in {{3, 4, 5}}, got x.shape={tuple(x.shape)}"
        )


def _is_single_distribution_input(
    x: torch.Tensor,
    *,
    image_dim: Optional[int] = None,
    single_distribution: Optional[bool] = None,
) -> bool:
    if x.ndim == 3:
        return True
    if x.ndim == 5:
        return False
    if x.ndim != 4:
        raise ValueError(
            f"Expected x.ndim in {{3, 4, 5}}, got x.shape={tuple(x.shape)}"
        )

    if single_distribution is not None:
        return single_distribution

    if image_dim is not None:
        batch_image_dim = x.shape[2] * x.shape[3]
        single_image_dim = x.shape[1] * x.shape[2] * x.shape[3]
        batch_matches = batch_image_dim == image_dim
        single_matches = single_image_dim == image_dim

        if batch_matches and not single_matches:
            return False
        if single_matches and not batch_matches:
            return True
        if not batch_matches and not single_matches:
            raise ValueError(
                "empirical_distributions has incompatible image dimensions for the "
                "fitted state. Pass `single_distribution` explicitly only if the "
                "4D tensor shape is ambiguous."
            )

    return x.shape[-1] in (1, 3)


def _validate_flattened_distributions(
    x: torch.Tensor,
    *,
    name: str,
    require_non_empty_batch: bool,
) -> None:
    if require_non_empty_batch and x.shape[0] == 0:
        raise ValueError(f"{name} must contain at least one distribution.")
    if x.shape[1] == 0:
        raise ValueError(f"{name} must contain at least one sample per distribution.")


def _median_heuristic_sigma(
    train_flat: torch.Tensor,
    max_points: int = 1024,
) -> float:
    """
    Choose RBF bandwidth sigma from a random subset of all training images.
    train_flat: [M, N, D]
    """
    x = train_flat.reshape(-1, train_flat.shape[-1])  # [M*N, D]
    num = min(max_points, x.shape[0])
    idx = torch.randperm(x.shape[0], device=x.device)[:num]
    z = x[idx]  # [num, D]

    # pairwise Euclidean distances
    dists = torch.cdist(z, z, p=2)
    vals = dists[dists > 0]

    if vals.numel() == 0:
        return 1.0

    return vals.median().item()


def _rbf_mean_kernel_between_sets(
    x: torch.Tensor,
    y: torch.Tensor,
    sigma: float,
    chunk_size: int = 256,
) -> torch.Tensor:
    """
    Compute
        (1 / (|x||y|)) sum_{a,b} exp(-||x_a - y_b||^2 / (2 sigma^2))

    x: [nx, D]
    y: [ny, D]
    returns: scalar tensor
    """
    if sigma <= 0:
        raise ValueError(f"sigma must be positive, got sigma={sigma}")
    if chunk_size <= 0:
        raise ValueError(f"chunk_size must be positive, got chunk_size={chunk_size}")
    if x.shape[0] == 0 or y.shape[0] == 0:
        raise ValueError("Kernel inputs must contain at least one sample.")

    sigma2 = float(sigma) ** 2
    total = x.new_tensor(0.0)

    for i in range(0, x.shape[0], chunk_size):
        xi = x[i:i + chunk_size]  # [bx, D]
        xi2 = (xi * xi).sum(dim=1, keepdim=True)  # [bx, 1]

        for j in range(0, y.shape[0], chunk_size):
            yj = y[j:j + chunk_size]  # [by, D]
            yj2 = (yj * yj).sum(dim=1, keepdim=True).T  # [1, by]

            d2 = (xi2 + yj2 - 2.0 * (xi @ yj.T)).clamp_min_(0.0)  # [bx, by]
            kij = torch.exp(-d2 / (2.0 * sigma2))
            total = total + kij.sum()

    return total / (x.shape[0] * y.shape[0])


@torch.no_grad()
def fit_kme_pca_state(
    train_set: torch.Tensor,
    embedding_dim: int,
    sigma: Optional[float] = None,
    sigma_num_points: int = 1024,
    chunk_size: int = 256,
    normalize: bool = False,
) -> Dict[str, Any]:
    """
    Build everything needed for KME-PCA embeddings.

    Args:
        train_set: [M, N, H, W] or [M, N, H, W, C]
        embedding_dim: target embedding dimension r
        sigma: RBF bandwidth; if None, use median heuristic
        sigma_num_points: number of images used to estimate sigma
        chunk_size: chunk size for pairwise kernel computations
        normalize:
            - False: uses the raw projection formula u = m^T alpha
              (closest to the formulas we discussed)
            - True: standard kernel-PCA style normalization by sqrt(eigenvalue)

    Returns:
        state: dict containing all quantities needed later
    """
    if embedding_dim <= 0:
        raise ValueError(
            f"embedding_dim must be positive, got embedding_dim={embedding_dim}"
        )
    if sigma is None and sigma_num_points <= 0:
        raise ValueError(
            f"sigma_num_points must be positive, got sigma_num_points={sigma_num_points}"
        )

    x = _flatten_distributions(train_set, single_distribution=False)  # [M, N, D]
    _validate_flattened_distributions(
        x,
        name="train_set",
        require_non_empty_batch=True,
    )
    M, N, D = x.shape

    if sigma is None:
        sigma = _median_heuristic_sigma(x, max_points=sigma_num_points)

    # Uncentered Gram matrix K, where
    # K[i,j] = <mu_{P_i}, mu_{P_j}>
    K = torch.empty((M, M), device=x.device, dtype=x.dtype)

    for i in range(M):
        K[i, i] = _rbf_mean_kernel_between_sets(
            x[i], x[i], sigma=sigma, chunk_size=chunk_size
        )
        for j in range(i + 1, M):
            val = _rbf_mean_kernel_between_sets(
                x[i], x[j], sigma=sigma, chunk_size=chunk_size
            )
            K[i, j] = val
            K[j, i] = val

    # Center the Gram matrix:
    # G = H K H
    col_mean = K.mean(dim=0)        # [M]
    row_mean = K.mean(dim=1)        # [M], same as col_mean up to numerics
    grand_mean = K.mean()           # scalar

    G = K - row_mean[:, None] - col_mean[None, :] + grand_mean
    G = 0.5 * (G + G.T)  # numerical symmetrization

    # Eigen-decomposition of centered Gram matrix
    eigvals, eigvecs = torch.linalg.eigh(G)  # ascending
    order = torch.argsort(eigvals, descending=True)
    eigvals = eigvals[order]
    eigvecs = eigvecs[:, order]

    # Keep positive eigenvalues only
    tol = max(1e-10, 1e-8 * eigvals.abs().max().item())
    keep_mask = eigvals > tol
    num_keep = int(keep_mask.sum().item())
    if num_keep == 0:
        raise RuntimeError("No positive eigenvalues found in centered Gram matrix.")

    r = min(embedding_dim, num_keep)
    eigvals = eigvals[:r]      # [r]
    eigvecs = eigvecs[:, :r]   # [M, r]

    # alpha^(l): coefficient vectors for the RKHS principal directions
    if normalize:
        alphas = eigvecs / torch.sqrt(eigvals.clamp_min(1e-12))[None, :]
    else:
        alphas = eigvecs

    # Training embeddings:
    # u(P_i) = G[i, :] @ alphas   (same as G @ alphas, row-wise)
    train_embeddings = G @ alphas  # [M, r]

    state = {
        "train_flat": x,                  # [M, N, D] -- needed for exact out-of-sample embedding
        "M": M,
        "N_train": N,
        "image_dim": D,
        "sigma": float(sigma),
        "chunk_size": int(chunk_size),
        "embedding_dim": int(r),
        "K": K,                           # [M, M], uncentered Gram
        "G": G,                           # [M, M], centered Gram
        "row_mean": row_mean,             # [M]
        "col_mean": col_mean,             # [M]
        "grand_mean": grand_mean,         # scalar
        "eigvals": eigvals,               # [r]
        "eigvecs": eigvecs,               # [M, r]
        "alphas": alphas,                 # [M, r]
        "train_embeddings": train_embeddings,  # [M, r]
        "normalize": bool(normalize),
    }
    return state


@torch.no_grad()
def compute_kme_embeddings(
    state: Dict[str, Any],
    empirical_distributions: Optional[torch.Tensor] = None,
    single_distribution: Optional[bool] = None,
) -> torch.Tensor:
    """
    Compute embeddings using a fitted KME-PCA state.

    Cases:
        1) empirical_distributions is None:
           returns training embeddings, shape [M, r]

        2) empirical_distributions.shape == [B, n, H, W]
           or [B, n, H, W, C]:
           returns embeddings for B distributions, shape [B, r]

        3) empirical_distributions.shape == [n, H, W]
           or [n, H, W, C]:
           returns one embedding, shape [r]

    Notes:
        - n can be different from the training N.
        - Exact out-of-sample embedding needs state["train_flat"].
        - For 4D inputs, `single_distribution` disambiguates between
          [B, n, H, W] and [n, H, W, C]. If left as None, the function first
          matches against `state["image_dim"]`; if that is still ambiguous,
          a last dimension of 1 or 3 is treated as a channel dimension.
    """
    if empirical_distributions is None:
        return state["train_embeddings"]

    is_single_distribution = _is_single_distribution_input(
        empirical_distributions,
        image_dim=state["image_dim"],
        single_distribution=single_distribution,
    )

    x_new = _flatten_distributions(
        empirical_distributions,
        single_distribution=is_single_distribution,
    ).to(
        device=state["train_flat"].device,
        dtype=state["train_flat"].dtype,
    )  # [B, n, D]
    _validate_flattened_distributions(
        x_new,
        name="empirical_distributions",
        require_non_empty_batch=False,
    )

    train_flat = state["train_flat"]   # [M, N, D]
    M = state["M"]
    sigma = state["sigma"]
    chunk_size = state["chunk_size"]
    col_mean = state["col_mean"]       # [M]
    grand_mean = state["grand_mean"]   # scalar
    alphas = state["alphas"]           # [M, r]

    B = x_new.shape[0]
    out = torch.empty(
        (B, alphas.shape[1]),
        device=x_new.device,
        dtype=x_new.dtype,
    )

    for b in range(B):
        # k_star[j] = <mu_{P_*}, mu_{P_j}>
        k_star = torch.empty((M,), device=x_new.device, dtype=x_new.dtype)

        for j in range(M):
            k_star[j] = _rbf_mean_kernel_between_sets(
                x_new[b],
                train_flat[j],
                sigma=sigma,
                chunk_size=chunk_size,
            )

        # Center the cross-vector consistently with training centering:
        # m_star(j) = k_star(j) - col_mean(j) - mean(k_star) + grand_mean
        m_star = k_star - col_mean - k_star.mean() + grand_mean  # [M]

        # u(P_*) = A^T m_star, where A = [alpha^(1), ..., alpha^(r)]
        out[b] = m_star @ alphas  # [r]

    if is_single_distribution:
        return out[0]  # [r]
    return out         # [B, r]
