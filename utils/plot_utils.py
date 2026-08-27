import matplotlib.pyplot as plt
import os
import numpy as np
from matplotlib import cm


def plot_ICL_results(ncols, prompts, samples, figsize=(4, 4), Nx=32, savepath=None):
    """Plot ICL results with exactly 2 rows: prompts (row 0) + generated (row 1).

    Supports inputs shaped (N, Nx, Nx) or (N, Nx, Nx, 1).
    """
    nrows = 2

    prompts = np.asarray(prompts)
    samples = np.asarray(samples)
    if prompts.ndim == 4 and prompts.shape[-1] == 1:
        prompts = prompts[..., 0]
    if samples.ndim == 4 and samples.shape[-1] == 1:
        samples = samples[..., 0]

    """
    Create grid of subplots:
      - (0,0) shows 'Prompt'
      - (1,0) shows 'DM gen'
      - Row 0, Col >=1 plots prompts[i]
      - Row 1, Col >=1 plots samples[i]

    prompts, samples: lists/arrays length = ncols-1
    """

    points_x_0 = np.linspace(0, 1, Nx)
    xx_0, yy_0 = np.meshgrid(points_x_0, points_x_0)

    fig, axes = plt.subplots(
        nrows=nrows, 
        ncols=ncols, 
        figsize=(figsize[0] * ncols, figsize[1] * nrows)
    )

    # --- Make axes always 2D ---
    if nrows == 1 and ncols == 1:
        axes = np.array([[axes]])
    elif nrows == 1:
        axes = axes.reshape(1, -1)
    elif ncols == 1:
        axes = axes.reshape(-1, 1)

    # --- Add text in first column ---
    axes[0, 0].text(0.5, 0.5, "Prompt", ha="center", va="center", fontsize=32)
    axes[0, 0].set_axis_off()

    axes[1, 0].text(0.5, 0.5, "ICL DM", ha="center", va="center", fontsize=32)
    axes[1, 0].set_axis_off()

    # --- Plot prompts on row 0, col 1..---
    for j in range(1, ncols):
        if j < prompts.shape[0] + 1:
            axes[0, j].contourf(xx_0, yy_0, prompts[j-1], 36,  cmap=cm.jet)
            axes[0, j].set_title(f"Prompt {j}", fontsize=24)
            axes[0, j].axis('off')
        else:
            axes[0, j].set_axis_off()

    # --- Plot samples on row 1, col 1..---
    for j in range(1, ncols):
        if j < samples.shape[0] + 1:
            axes[1, j].contourf(xx_0, yy_0, samples[j-1], 36, cmap=cm.jet)
            axes[1, j].set_title(f"Sample {j}", fontsize=24)
            axes[1, j].axis('off')
        else:
            axes[1, j].set_axis_off()

    plt.tight_layout()
    plt.show()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')


def plot_ICL_results_real_image(ncols, prompts, samples, figsize=(4, 4), savepath=None):
    """Plot ICL results (real images) with exactly 2 rows: prompts + generated."""
    nrows = 2
    """
    Create grid of subplots:
      - (0,0) shows 'Prompt'
      - (1,0) shows 'DM gen'
      - Row 0, Col >=1 plots prompts[i]
      - Row 1, Col >=1 plots samples[i]

    prompts, samples: lists/arrays length = ncols-1
    """

    fig, axes = plt.subplots(
        nrows=nrows, 
        ncols=ncols, 
        figsize=(figsize[0] * ncols, figsize[1] * nrows)
    )

    # --- Make axes always 2D ---
    if nrows == 1 and ncols == 1:
        axes = np.array([[axes]])
    elif nrows == 1:
        axes = axes.reshape(1, -1)
    elif ncols == 1:
        axes = axes.reshape(-1, 1)

    # --- Add text in first column ---
    axes[0, 0].text(0.5, 0.5, "Prompt", ha="center", va="center", fontsize=16)
    axes[0, 0].set_axis_off()

    axes[1, 0].text(0.5, 0.5, "DM gen", ha="center", va="center", fontsize=16)
    axes[1, 0].set_axis_off()

    # --- Plot prompts on row 0, col 1..---
    for j in range(1, ncols):
        if j < prompts.shape[0] + 1:
            axes[0, j].imshow(prompts[j-1], cmap='plasma', vmin=-1, vmax=1)
            axes[0, j].set_title(f"Prompt {j}")
            axes[0, j].axis('off')
        else:
            axes[0, j].set_axis_off()

    # --- Plot samples on row 1, col 1..---
    for j in range(1, ncols):
        axes[1, j].imshow(samples[j-1], cmap='plasma', vmin=-1, vmax=1)
        axes[1, j].set_title(f"Gen Sample {j}")
        axes[1, j].axis('off')

    plt.tight_layout()
    plt.show()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')



def plot_PDF(spectrum_sample, spectrum_ref, figsize=(4, 4), savepath=None):
    num_points = len(spectrum_sample)
    grid = np.linspace(-1, 1, num_points)
    """Plot PDF of spectrum_sample and spectrum_ref."""
    fig, ax = plt.subplots(figsize=figsize)

    ax.plot(grid, spectrum_ref, label='Reference', color='blue', linewidth=2)
    ax.plot(grid, spectrum_sample, label='Sample', color='red', linewidth=2)
    ax.set_xlabel(r'$u$', fontsize=12)
    ax.set_ylabel(r'$PDF(u)$', fontsize=12)
    ax.legend(fontsize=10)
    plt.tight_layout()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')

# def plot_spectra(spectrum_sample, spectrum_ref, figsize=(4, 4), savepath=None):
#     """Plot spectra of sample and reference."""
#     num_points = len(spectrum_sample)
#     grid = np.arange(num_points)

#     fig, ax = plt.subplots(figsize=figsize)
#     ax.plot(grid, spectrum_ref, label='Reference', color='blue', linewidth=2)
#     ax.plot(grid, spectrum_sample, label='Sample', color='red', linewidth=2)
#     ax.set_xlabel(r'$k$', fontsize=18)
#     ax.set_ylabel(r'$E(k)$', fontsize=18)
#     ax.set_yscale('log')
#     ax.legend(fontsize=24)
#     plt.tight_layout()

#     if savepath is not None:
#         fig.savefig(savepath, dpi=300, bbox_inches='tight')

def plot_spectra(spectrum_sample, spectrum_ref, figsize=(4, 4), savepath=None, eps=1e-8):
    """Plot log ratio of energy spectra: log(E_sample / E_ref)."""
    num_points = len(spectrum_sample)
    grid = np.arange(num_points)

    log_ratio = np.abs(np.log((np.asarray(spectrum_sample) + eps) / (np.asarray(spectrum_ref) + eps)))

    fig, ax = plt.subplots(figsize=figsize)
    ax.plot(grid[1:], log_ratio[1:], color='red', linewidth=2)
    ax.set_xlabel(r'$k$', fontsize=12)
    ax.set_ylabel(r'$|\log(E_k / E^{\mathrm{ref}}_k)|$', fontsize=12)
    ax.set_ylim(0, np.max(log_ratio[1:]) * 1.5)
    ax.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
    plt.tight_layout()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
















def plot_ICL_results_two(ncols, prompts, samples, samples_cond, figsize=(4, 4), Nx=32, savepath=None):
    """Plot ICL results with exactly 2 rows: prompts (row 0) + generated (row 1).

    Supports inputs shaped (N, Nx, Nx) or (N, Nx, Nx, 1).
    """
    nrows = 3

    prompts = np.asarray(prompts)
    samples = np.asarray(samples)
    if prompts.ndim == 4 and prompts.shape[-1] == 1:
        prompts = prompts[..., 0]
    if samples.ndim == 4 and samples.shape[-1] == 1:
        samples = samples[..., 0]
    if samples_cond.ndim == 4 and samples_cond.shape[-1] == 1:
        samples_cond = samples_cond[..., 0]

    """
    Create grid of subplots:
      - (0,0) shows 'Prompt'
      - (1,0) shows 'ICL gen'
      - (2,0) shows 'DM cond gen'
      - Row 0, Col >=1 plots prompts[i]
      - Row 1, Col >=1 plots samples[i]
      - Row 2, Col >=1 plots samples_cond[i]

    prompts, samples: lists/arrays length = ncols-1
    """

    points_x_0 = np.linspace(0, 1, Nx)
    xx_0, yy_0 = np.meshgrid(points_x_0, points_x_0)

    fig, axes = plt.subplots(
        nrows=nrows, 
        ncols=ncols, 
        figsize=(figsize[0] * ncols, figsize[1] * nrows)
    )

    # --- Make axes always 2D ---
    if nrows == 1 and ncols == 1:
        axes = np.array([[axes]])
    elif nrows == 1:
        axes = axes.reshape(1, -1)
    elif ncols == 1:
        axes = axes.reshape(-1, 1)

    # --- Add text in first column ---
    axes[0, 0].text(0.5, 0.5, "Prompt", ha="center", va="center", fontsize=32)
    axes[0, 0].set_axis_off()

    axes[1, 0].text(0.5, 0.5, "ICL DM", ha="center", va="center", fontsize=32)
    axes[1, 0].set_axis_off()

    axes[2, 0].text(0.5, 0.5, "DM Cond Gen", ha="center", va="center", fontsize=32)
    axes[2, 0].set_axis_off()

    # --- Plot prompts on row 0, col 1..---
    for j in range(1, ncols):
        if j < prompts.shape[0] + 1:
            axes[0, j].contourf(xx_0, yy_0, prompts[j-1], 36,  cmap=cm.jet)
            #axes[0, j].set_title(f"Prompt {j}", fontsize=24)
            axes[0, j].axis('off')
        else:
            axes[0, j].set_axis_off()

    # --- Plot samples on row 1, col 1..---
    for j in range(1, ncols):
        if j < samples.shape[0] + 1:
            axes[1, j].contourf(xx_0, yy_0, samples[j-1], 36, cmap=cm.jet)
            #axes[1, j].set_title(f"Sample {j}", fontsize=24)
            axes[1, j].axis('off')
        else:
            axes[1, j].set_axis_off()

    # --- Plot samples_cond on row 2, col 1..---
    for j in range(1, ncols):
        if j < samples_cond.shape[0] + 1:
            axes[2, j].contourf(xx_0, yy_0, samples_cond[j-1], 36, cmap=cm.jet)
            #axes[2, j].set_title(f"Sample Cond {j}", fontsize=24)
            axes[2, j].axis('off')
        else:
            axes[2, j].set_axis_off()

    plt.tight_layout()
    plt.show()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')



def plot_PDF_two(spectrum_sample, spectrum_sample_cond, spectrum_ref, figsize=(4, 4), savepath=None):
    num_points = len(spectrum_sample)
    grid = np.linspace(-1, 1, num_points)
    """Plot PDF of spectrum_sample and spectrum_ref."""
    fig, ax = plt.subplots(figsize=figsize)

    ax.plot(grid, spectrum_ref, label='Ref', color='blue', linewidth=2)
    ax.plot(grid, spectrum_sample, label='ICL DM', color='red', linewidth=2)
    ax.plot(grid, spectrum_sample_cond, label='Cond DM', color='green', linewidth=2)
    ax.set_xlabel(r'$u$', fontsize=12)
    ax.set_ylabel(r'$PDF(u)$', fontsize=12)
    ax.legend(fontsize=10, loc='upper center', bbox_to_anchor=(0.5, 1.15), ncol=3, frameon=False)
    plt.tight_layout()

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')

def plot_spectra_two(spectrum_sample, spectrum_sample_cond, spectrum_ref, figsize=(4, 4), savepath=None, eps=1e-8):
    """Plot log ratio of energy spectra: log(E_sample / E_ref)."""
    num_points = len(spectrum_sample)
    grid = np.arange(num_points)

    log_ratio = np.abs(np.log((np.asarray(spectrum_sample) + eps) / (np.asarray(spectrum_ref) + eps)))

    log_ratio_cond = np.abs(np.log((np.asarray(spectrum_sample_cond) + eps) / (np.asarray(spectrum_ref) + eps)))

    fig, ax = plt.subplots(figsize=figsize)
    ax.plot(grid[1:], log_ratio[1:],      color='red',   linewidth=2, label='ICL DM')
    ax.plot(grid[1:], log_ratio_cond[1:], color='green', linewidth=2, label='Cond DM')
    ax.set_xlabel(r'$k$', fontsize=12)
    ax.set_ylabel(r'$|\log(E_k / E^{\mathrm{ref}}_k)|$', fontsize=12)
    ax.set_ylim(0, max(np.max(log_ratio[1:]), np.max(log_ratio_cond[1:])) * 1.5)
    ax.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
    ax.legend(fontsize=10, loc='upper center', bbox_to_anchor=(0.5, 1.15), ncol=2, frameon=False)
    plt.tight_layout()
 

    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')


def plot_ICL_results_real_image_two(ncols, prompts, samples, sample_cond, figsize=(4, 4), savepath=None):
    """Plot ICL results (real images) with 3 rows: prompts + ICL DM + Cond DM."""
    nrows = 3

    prompts = np.asarray(prompts)
    samples = np.asarray(samples)
    sample_cond = np.asarray(sample_cond)
    if prompts.ndim == 4 and prompts.shape[-1] == 1:
        prompts = prompts[..., 0]
    if samples.ndim == 4 and samples.shape[-1] == 1:
        samples = samples[..., 0]
    if sample_cond.ndim == 4 and sample_cond.shape[-1] == 1:
        sample_cond = sample_cond[..., 0]

    fig, axes = plt.subplots(nrows=nrows, ncols=ncols, figsize=(figsize[0] * ncols, figsize[1] * nrows))

    if ncols == 1:
        axes = axes.reshape(-1, 1)

    axes[0, 0].text(0.5, 0.5, "Prompt",  ha="center", va="center", fontsize=16); axes[0, 0].set_axis_off()
    axes[1, 0].text(0.5, 0.5, "ICL DM",  ha="center", va="center", fontsize=16); axes[1, 0].set_axis_off()
    axes[2, 0].text(0.5, 0.5, "Cond DM", ha="center", va="center", fontsize=16); axes[2, 0].set_axis_off()

    for j in range(1, ncols):
        if j < prompts.shape[0] + 1:
            axes[0, j].imshow(prompts[j-1], vmin=-1, vmax=1)
        axes[0, j].axis('off')

    for j in range(1, ncols):
        if j - 1 < samples.shape[0]:
            axes[1, j].imshow(samples[j-1], vmin=-1, vmax=1)
        axes[1, j].axis('off')

    for j in range(1, ncols):
        if j - 1 < sample_cond.shape[0]:
            axes[2, j].imshow(sample_cond[j-1], vmin=-1, vmax=1)
        axes[2, j].axis('off')

    plt.tight_layout()
    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
    plt.close(fig)


def plot_ICL_results_real_image_three(ncols, prompts, samples, sample_cond, sample_sno, figsize=(4, 4), savepath=None):
    """Plot ICL results (real images) with 4 rows: prompts + ICL DM + Cond DM + SNO."""
    nrows = 4

    prompts     = np.asarray(prompts)
    samples     = np.asarray(samples)
    sample_cond = np.asarray(sample_cond)
    sample_sno  = np.asarray(sample_sno)

    if prompts.ndim == 4 and prompts.shape[-1] == 1:
        prompts = prompts[..., 0]
    if samples.ndim == 4 and samples.shape[-1] == 1:
        samples = samples[..., 0]
    if sample_cond.ndim == 4 and sample_cond.shape[-1] == 1:
        sample_cond = sample_cond[..., 0]
    if sample_sno.ndim == 4 and sample_sno.shape[-1] == 1:
        sample_sno = sample_sno[..., 0]

    fig, axes = plt.subplots(nrows=nrows, ncols=ncols,
                             figsize=(figsize[0] * ncols, figsize[1] * nrows))
    if ncols == 1:
        axes = axes.reshape(-1, 1)

    axes[0, 0].text(0.5, 0.5, "Prompt",  ha="center", va="center", fontsize=40, fontweight='bold'); axes[0, 0].set_axis_off()
    axes[1, 0].text(0.5, 0.5, "ICL DM",  ha="center", va="center", fontsize=40, fontweight='bold'); axes[1, 0].set_axis_off()
    axes[2, 0].text(0.5, 0.5, "Cond DM", ha="center", va="center", fontsize=40, fontweight='bold'); axes[2, 0].set_axis_off()
    axes[3, 0].text(0.5, 0.5, "SNO",     ha="center", va="center", fontsize=40, fontweight='bold'); axes[3, 0].set_axis_off()

    for j in range(1, ncols):
        if j - 1 < prompts.shape[0]:
            axes[0, j].imshow(np.clip(prompts[j-1], 0, 1))
        axes[0, j].axis('off')

    for j in range(1, ncols):
        if j - 1 < samples.shape[0]:
            axes[1, j].imshow(np.clip(samples[j-1], 0, 1))
        axes[1, j].axis('off')

    for j in range(1, ncols):
        if j - 1 < sample_cond.shape[0]:
            axes[2, j].imshow(np.clip(sample_cond[j-1], 0, 1))
        axes[2, j].axis('off')

    for j in range(1, ncols):
        if j - 1 < sample_sno.shape[0]:
            axes[3, j].imshow(np.clip(sample_sno[j-1], 0, 1))
        axes[3, j].axis('off')

    plt.tight_layout()
    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
    plt.close(fig)


def plot_scientific_images_three(ncols, prompts, samples, sample_cond, sample_sno,
                                  Nx=128, figsize=(4, 4), cmap=cm.jet, savepath=None):
    """Plot 4 rows of scalar-field images using contourf (for NS, ERA5, GRF, etc.).

    Row 0: Prompt / reference
    Row 1: ICL DM
    Row 2: Cond DM
    Row 3: SNO

    Inputs shaped (N, Nx, Nx) or (N, Nx, Nx, 1).
    """
    nrows = 4

    def _squeeze(x):
        x = np.asarray(x)
        if x.ndim == 4 and x.shape[-1] == 1:
            x = x[..., 0]
        return x

    prompts     = _squeeze(prompts)
    samples     = _squeeze(samples)
    sample_cond = _squeeze(sample_cond)
    sample_sno  = _squeeze(sample_sno)

    points = np.linspace(0, 1, Nx)
    xx, yy = np.meshgrid(points, points)

    fig, axes = plt.subplots(nrows=nrows, ncols=ncols,
                             figsize=(figsize[0] * ncols, figsize[1] * nrows))
    if ncols == 1:
        axes = axes.reshape(-1, 1)

    row_labels = ["Prompt", "ICL DM", "Cond DM", "SNO"]
    row_data   = [prompts, samples, sample_cond, sample_sno]

    for r, (label, data) in enumerate(zip(row_labels, row_data)):
        axes[r, 0].text(0.5, 0.5, label, ha="center", va="center",
                        fontsize=40, fontweight='bold')
        axes[r, 0].set_axis_off()
        for j in range(1, ncols):
            if j - 1 < data.shape[0]:
                axes[r, j].contourf(xx, yy, data[j - 1], 36, cmap=cmap)
            axes[r, j].set_axis_off()

    plt.tight_layout()
    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
    plt.close(fig)


def plot_spectra_three(spectrum_sample, spectrum_cond, spectrum_sno, spectrum_ref,
                       labels=('ICL DM', 'Cond DM', 'SNO'),
                       figsize=(5, 4), savepath=None, eps=1e-8):
    """Plot log ratio of energy spectra for 3 methods vs reference."""
    grid = np.arange(len(spectrum_sample))

    log_ratio_icl  = np.abs(np.log((np.asarray(spectrum_sample) + eps) / (np.asarray(spectrum_ref) + eps)))
    log_ratio_cond = np.abs(np.log((np.asarray(spectrum_cond)   + eps) / (np.asarray(spectrum_ref) + eps)))
    log_ratio_sno  = np.abs(np.log((np.asarray(spectrum_sno)    + eps) / (np.asarray(spectrum_ref) + eps)))

    fig, ax = plt.subplots(figsize=figsize)
    ax.plot(grid[1:], log_ratio_icl[1:],  color='red',    linewidth=2, label=labels[0])
    ax.plot(grid[1:], log_ratio_cond[1:], color='green',  linewidth=2, label=labels[1])
    ax.plot(grid[1:], log_ratio_sno[1:],  color='purple', linewidth=2, label=labels[2])
    ax.set_xlabel(r'$k$', fontsize=12)
    ax.set_ylabel(r'$|\log(E_k / E^{\mathrm{ref}}_k)|$', fontsize=12)
    ymax = max(log_ratio_icl[1:].max(), log_ratio_cond[1:].max(), log_ratio_sno[1:].max())
    ax.set_ylim(0, ymax * 1.5)
    ax.xaxis.set_major_locator(plt.MaxNLocator(integer=True))
    ax.legend(fontsize=12, loc='upper center', bbox_to_anchor=(0.5, 1.15),
              ncol=3, frameon=False)
    plt.tight_layout()
    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
    plt.close(fig)


def plot_PDF_three(spectrum_sample, spectrum_cond, spectrum_sno, spectrum_ref,
                   labels=('ICL DM', 'Cond DM', 'SNO'),
                   figsize=(5, 4), savepath=None):
    """Plot PDF for 3 methods vs reference."""
    num_points = len(spectrum_sample)
    grid = np.linspace(-1, 1, num_points)

    fig, ax = plt.subplots(figsize=figsize)
    ax.plot(grid, spectrum_ref,    color='blue',   linewidth=2, label='Ref')
    ax.plot(grid, spectrum_sample, color='red',    linewidth=2, label=labels[0])
    ax.plot(grid, spectrum_cond,   color='green',  linewidth=2, label=labels[1])
    ax.plot(grid, spectrum_sno,    color='purple', linewidth=2, label=labels[2])
    ax.set_xlabel(r'$u$', fontsize=12)
    ax.set_ylabel(r'$PDF(u)$', fontsize=12)
    ax.legend(fontsize=12, loc='upper center', bbox_to_anchor=(0.5, 1.25),
              ncol=2, frameon=False)
    plt.tight_layout()
    if savepath is not None:
        fig.savefig(savepath, dpi=300, bbox_inches='tight')
    plt.close(fig)