import numpy as np
from scipy import linalg

import torch
import torch.nn as nn
import torch.nn.functional as F
from torch.utils.data import DataLoader
from torchvision.models import inception_v3, Inception_V3_Weights


class InceptionV3FID(nn.Module):
    """
    Standard FID feature extractor based on pretrained Inception-V3.
    Returns 2048-d pooled features.
    """
    def __init__(self):
        super().__init__()
        weights = Inception_V3_Weights.IMAGENET1K_V1
        model = inception_v3(weights=weights, transform_input=False)
        model.fc = nn.Identity()
        self.model = model.eval()

        self.register_buffer(
            "mean",
            torch.tensor([0.485, 0.456, 0.406]).view(1, 3, 1, 1)
        )
        self.register_buffer(
            "std",
            torch.tensor([0.229, 0.224, 0.225]).view(1, 3, 1, 1)
        )

    @torch.no_grad()
    def forward(self, x):
        """
        x: [B,1,H,W] or [B,3,H,W], expected in [0,1]
        returns: [B,2048]
        """
        if x.shape[1] == 1:
            x = x.repeat(1, 3, 1, 1)

        x = F.interpolate(x, size=(299, 299), mode="bilinear", align_corners=False)
        x = (x - self.mean) / self.std
        feat = self.model(x)
        return feat


def load_inception_fid_model(device=None):
    if device is None:
        device = "cuda" if torch.cuda.is_available() else "cpu"
    model = InceptionV3FID().to(device).eval()
    return model


@torch.no_grad()
def extract_inception_features(x, model, batch_size=128, device=None):
    """
    x: [N,H,W,1] or [N,H,W,3]
    returns: [N,2048]
    """
    if device is None:
        device = next(model.parameters()).device

    if isinstance(x, np.ndarray):
        x = torch.from_numpy(x).float()
    else:
        x = x.float()

    if x.ndim != 4:
        raise ValueError(f"Expected x with shape [N,H,W,C], got {tuple(x.shape)}")
    if x.shape[-1] not in [1, 3]:
        raise ValueError(f"Expected last channel 1 or 3, got {x.shape[-1]}")

    x = x.permute(0, 3, 1, 2).contiguous()   # [N,C,H,W]
    loader = DataLoader(x, batch_size=batch_size, shuffle=False, drop_last=False)

    feats = []
    model.eval()
    for xb in loader:
        xb = xb.to(device)
        fb = model(xb)
        feats.append(fb.cpu().numpy())

    return np.concatenate(feats, axis=0)


def compute_stats(feats):
    mu = np.mean(feats, axis=0)
    sigma = np.cov(feats, rowvar=False)
    return mu, sigma


def frechet_distance(mu1, sigma1, mu2, sigma2, eps=1e-6):
    """
    Standard FID formula:
        ||mu1-mu2||^2 + Tr(sigma1 + sigma2 - 2 (sigma1 sigma2)^{1/2})
    """
    diff = mu1 - mu2
    covmean, _ = linalg.sqrtm(sigma1 @ sigma2, disp=False)

    if not np.isfinite(covmean).all():
        offset = np.eye(sigma1.shape[0]) * eps
        covmean = linalg.sqrtm((sigma1 + offset) @ (sigma2 + offset))

    if np.iscomplexobj(covmean):
        covmean = covmean.real

    fid = diff @ diff + np.trace(sigma1) + np.trace(sigma2) - 2.0 * np.trace(covmean)
    return float(fid)


def compute_fid_inception(x_gen, x_ref, batch_size=128, device=None):
    """
    x_gen: [N,H,W,1] or [N,H,W,3]
    x_ref: [M,H,W,1] or [M,H,W,3]

    Assumes pixel values are in [0,1].
    If your data is in [-1,1], first rescale by (x+1)/2.
    """
    model = load_inception_fid_model(device=device)

    feats_gen = extract_inception_features(x_gen, model, batch_size=batch_size, device=device)
    feats_ref = extract_inception_features(x_ref, model, batch_size=batch_size, device=device)

    mu_gen, sigma_gen = compute_stats(feats_gen)
    mu_ref, sigma_ref = compute_stats(feats_ref)

    return frechet_distance(mu_gen, sigma_gen, mu_ref, sigma_ref)