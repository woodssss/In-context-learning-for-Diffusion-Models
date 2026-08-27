import functools
import torch
from torch.optim import Adam
from tqdm import tqdm
import matplotlib.pyplot as plt
import os
from torch.utils.data import DataLoader, TensorDataset
import argparse
from config.model_config_vpsde import *
import matplotlib.pyplot as plt
from matplotlib import cm
from utils.data_utils import gen_dataset_one, gen_dataset_one_ood, grf_laplacian_2d_batch
from utils.utils import make_image, make_image_meta
from utils.train_ICL_utils import loss_score_t, ode_solver
from utils.plot_utils import plot_ICL_results, plot_scientific_images_three, plot_spectra_three, plot_PDF_three
from utils.metric_utils import w2_pot, mmd_rbf, melr, pdf_kde, jsd_kde
from scipy.stats import gaussian_kde
from utils.fid_utils_imagenet import compute_fid_inception

device = torch.device("cuda" if torch.cuda.is_available() else "cpu")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='In-context in-distribution generation - NS')
    parser.add_argument('--K',     type=int, default=10,   help='Number of classes')
    parser.add_argument('--B',     type=int, default=1000, help='Number of images per class')
    parser.add_argument('--n',     type=int, default=10,   help='Number of prompt images for training')
    parser.add_argument('--m',     type=int, default=10,   help='Number of prompt images for inference')
    parser.add_argument('--nx',    type=int, default=128,  help='Image spatial size')
    parser.add_argument('--bs',    type=int, default=32,   help='Batch size for inference')
    parser.add_argument('--epoch', type=int, default=2000, help='Epoch number')
    parser.add_argument('--np',    type=int, default=2,    help='Number of prompt sets')
    parser.add_argument('--idx',   type=int, default=-1,   help='Inference index (-1 = run all 5)')
    args = parser.parse_args()

    K           = args.K
    B           = args.B
    n           = args.n
    Nx          = args.nx
    m           = args.m
    bs          = args.bs
    epoch       = args.epoch
    num_prompts = args.np
    idx_arg     = args.idx

    ### NS data ###
    data_name = f'data/NS_train_K{K}_B{B}.npy'
    with open(data_name, 'rb') as f:
        c = np.load(f)
    c = c.astype(np.float32)
    print(f"Loaded NS data with shape: {c.shape}")

    if c.ndim == 4:
        c = make_image_meta(c)  # (Nc, B, Nx, Nx)
        c = c[..., None]        # (Nc, B, Nx, Nx, 1)

    ### load KME embeddings for SNO ###
    embed_name = 'data/NS_KMEresults.npz'
    kme_state  = np.load(embed_name)
    embeddings = kme_state['train_embeddings']  # [K_total, embed_dim]
    print(f"Loaded KME embeddings with shape: {embeddings.shape}")

    load_mdl_name     = f'/mdls/NS_Gen_K_{K}_B_{B}_n_{n}_np_{num_prompts}_epoch_{epoch}_ckpt.pt'
    load_condmdl_name = f'/mdls/NS_cond_Gen_K_{K}_B_{B}_n_{n}_np_{num_prompts}_epoch_{epoch}_ckpt.pt'
    load_SNOmdl_name  = f'/mdls/NS_SNO_Gen_K_{K}_B_{B}_n_{n}_np_{num_prompts}_epoch_{epoch}_ckpt.pt'
    save_name_base = f'IND_NS_K_{K}_B_{B}_n_{n}_m_{m}_np_{num_prompts}_epoch_{epoch}'

    ### load models ###
    mdl      = torch.load(os.getcwd() + load_mdl_name,     weights_only=False, map_location=device); mdl.eval()
    mdl_cond = torch.load(os.getcwd() + load_condmdl_name, weights_only=False, map_location=device); mdl_cond.eval()
    mdl_sno  = torch.load(os.getcwd() + load_SNOmdl_name,  weights_only=False, map_location=device); mdl_sno.eval()

    ### start inference ###
    train = torch.from_numpy(c).float()
    cwd   = os.getcwd()
    log_path = cwd + '/logs/' + save_name_base + '.txt'
    os.makedirs(cwd + '/logs', exist_ok=True)
    os.makedirs(cwd + '/figs', exist_ok=True)

    with open(log_path, 'a') as log_f:
        idx_list = list(range(5)) if idx_arg == -1 else [idx_arg]
        for idx in tqdm(idx_list):
            save_name = save_name_base if idx_arg == -1 else save_name_base + f'_idx_{idx_arg}'
            idxs_prompt = np.random.choice(B, m, replace=False)
            prompts     = train[idx, idxs_prompt, ...].to(device)   # [m, 128, 128, 1]

            idxs_ref    = torch.randperm(train.shape[1])
            ref_samples = train[idx, idxs_ref, ...].to(device)      # [B, 128, 128, 1]

            noise = torch.randn(bs, Nx, Nx, 1).to(device)

            # ── ICL DM & Cond DM (image-prompt path) ──────────────────────
            chunk_size = 20
            def run_solver(mdl_):
                if bs <= chunk_size:
                    return ode_solver(mdl_, marginal_prob_fn, get_sde_forward_fn,
                                      noise, prompts,
                                      forward=2, eps=1e-5, use_em=True, num_steps=500)
                chunks = []
                for start in range(0, bs, chunk_size):
                    chunks.append(ode_solver(mdl_, marginal_prob_fn, get_sde_forward_fn,
                                             noise[start:start+chunk_size], prompts,
                                             forward=2, eps=1e-5, use_em=True, num_steps=500))
                return torch.cat(chunks, dim=0)

            sample_f      = run_solver(mdl)
            cond_sample_f = run_solver(mdl_cond)

            # ── SNO (KME embedding path) ───────────────────────────────────
            kme_vec   = torch.from_numpy(embeddings[idx]).float().to(device)  # [embed_dim]
            kme_batch = kme_vec.unsqueeze(0).expand(bs, -1)                   # [bs, embed_dim]

            def run_sno_solver():
                if bs <= chunk_size:
                    return ode_solver(mdl_sno, marginal_prob_fn, get_sde_forward_fn,
                                      noise, kme_batch,
                                      forward=2, eps=1e-5, use_em=True, num_steps=500)
                chunks = []
                for start in range(0, bs, chunk_size):
                    kme_chunk = kme_batch[start:start+chunk_size]
                    chunks.append(ode_solver(mdl_sno, marginal_prob_fn, get_sde_forward_fn,
                                             noise[start:start+chunk_size], kme_chunk,
                                             forward=2, eps=1e-5, use_em=True, num_steps=500))
                return torch.cat(chunks, dim=0)

            sno_sample_f = run_sno_solver()

            # ── normalize ──────────────────────────────────────────────────
            def normalize(x):
                ma = x.view(x.shape[0], -1).abs().max(dim=1).values.view(-1, 1, 1, 1)
                return x / (ma + 1e-8)
            sample_f      = normalize(sample_f)
            cond_sample_f = normalize(cond_sample_f)
            sno_sample_f  = normalize(sno_sample_f)

            # ── plotting (3 methods) ───────────────────────────────────────
            show_number = 10
            fig_path = cwd + '/figs/' + save_name + '_idx_' + str(idx) + '.png'
            plot_scientific_images_three(
                ncols=show_number,
                prompts=ref_samples[:show_number, ...].detach().cpu().numpy(),
                samples=sample_f[:show_number, ...].detach().cpu().numpy(),
                sample_cond=cond_sample_f[:show_number, ...].detach().cpu().numpy(),
                sample_sno=sno_sample_f[:show_number, ...].detach().cpu().numpy(),
                savepath=fig_path,
            )
            print(f"Saved figure to {fig_path}")

            print("max abs:", np.max(np.abs(sample_f.detach().cpu().numpy())),
                              np.max(np.abs(ref_samples[:bs].detach().cpu().numpy())))

            ref_np    = ref_samples[:bs].detach().cpu().numpy()
            sample_np = sample_f.detach().cpu().numpy()
            cond_np   = cond_sample_f.detach().cpu().numpy()
            sno_np    = sno_sample_f.detach().cpu().numpy()

            # ── metrics: ICL DM ────────────────────────────────────────────
            mmd             = mmd_rbf(ref_np, sample_np, l=0.01)
            w2              = w2_pot(ref_np,  sample_np)
            melrw_score, spectrum_sample, spectrum_ref = melr(sample_np, ref_np, num_modes=12, weights="weighted", return_spectra=True)
            melru_score     = melr(sample_np, ref_np, num_modes=12, weights="uniform")
            jsd             = jsd_kde(sample_np, ref_np)
            fid             = compute_fid_inception(x_gen=sample_np, x_ref=ref_np, batch_size=32, device=device)

            # ── metrics: Cond DM ───────────────────────────────────────────
            cond_mmd        = mmd_rbf(ref_np, cond_np, l=0.01)
            cond_w2         = w2_pot(ref_np,  cond_np)
            cond_melrw_score, spectrum_cond, _ = melr(cond_np, ref_np, num_modes=12, weights="weighted", return_spectra=True)
            cond_melru_score = melr(cond_np, ref_np, num_modes=12, weights="uniform")
            cond_jsd        = jsd_kde(cond_np, ref_np)
            cond_fid        = compute_fid_inception(x_gen=cond_np, x_ref=ref_np, batch_size=32, device=device)

            # ── metrics: SNO ───────────────────────────────────────────────
            sno_mmd         = mmd_rbf(ref_np, sno_np, l=0.01)
            sno_w2          = w2_pot(ref_np,  sno_np)
            sno_melrw_score, spectrum_sno, _ = melr(sno_np, ref_np, num_modes=12, weights="weighted", return_spectra=True)
            sno_melru_score = melr(sno_np, ref_np, num_modes=12, weights="uniform")
            sno_jsd         = jsd_kde(sno_np, ref_np)
            sno_fid         = compute_fid_inception(x_gen=sno_np, x_ref=ref_np, batch_size=32, device=device)

            # ── spectra & PDF plots ────────────────────────────────────────
            plot_spectra_three(
                spectrum_sample, spectrum_cond, spectrum_sno, spectrum_ref,
                labels=['ICL DM', 'Cond DM', 'SNO'],
                savepath=cwd + '/figs/' + save_name + f'_idx_{idx}_spectra.png',
            )
            _, pdf_sample = pdf_kde(sample_np)
            _, pdf_cond   = pdf_kde(cond_np)
            _, pdf_sno    = pdf_kde(sno_np)
            _, pdf_ref_   = pdf_kde(ref_np)
            plot_PDF_three(
                pdf_sample, pdf_cond, pdf_sno, pdf_ref_,
                labels=['ICL DM', 'Cond DM', 'SNO'],
                savepath=cwd + '/figs/' + save_name + f'_idx_{idx}_pdf.png',
            )

            # ── logging ────────────────────────────────────────────────────
            print(f"[idx={idx}] ICL  MMD={mmd:.4f}      W2={w2:.4f}      MELRw={melrw_score:.4f}      MELRu={melru_score:.4f}      JSD={jsd:.4f}      FID={fid:.4f}")
            print(f"[idx={idx}] Cond MMD={cond_mmd:.4f} W2={cond_w2:.4f} MELRw={cond_melrw_score:.4f} MELRu={cond_melru_score:.4f} JSD={cond_jsd:.4f} FID={cond_fid:.4f}")
            print(f"[idx={idx}] SNO  MMD={sno_mmd:.4f}  W2={sno_w2:.4f}  MELRw={sno_melrw_score:.4f}  MELRu={sno_melru_score:.4f}  JSD={sno_jsd:.4f}  FID={sno_fid:.4f}")
            log_f.write(f"idx={idx} ICL  MMD={mmd:.6f} W2={w2:.6f} MELRw={melrw_score:.6f} MELRu={melru_score:.6f} JSD={jsd:.6f} FID={fid:.6f}\n")
            log_f.write(f"idx={idx} Cond MMD={cond_mmd:.6f} W2={cond_w2:.6f} MELRw={cond_melrw_score:.6f} MELRu={cond_melru_score:.6f} JSD={cond_jsd:.6f} FID={cond_fid:.6f}\n")
            log_f.write(f"idx={idx} SNO  MMD={sno_mmd:.6f} W2={sno_w2:.6f} MELRw={sno_melrw_score:.6f} MELRu={sno_melru_score:.6f} JSD={sno_jsd:.6f} FID={sno_fid:.6f}\n")
            log_f.flush()

    print(f"Saved all metrics to {log_path}")
