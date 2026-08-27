import torch
from utils.KME_utils import fit_kme_pca_state, compute_kme_embeddings
import numpy as np
import argparse
from utils.utils import make_image, make_image_meta


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Generate Gaussian image dataset')
    parser.add_argument('--K', type=int, default=100, help='Number of classes')
    parser.add_argument('--B', type=int, default=1000, help='Number of images per class')
    parser.add_argument('--flag', type=int, default=5, help='problem type')
    args = parser.parse_args()

    sde = 'vp'

    K = args.K  # number of classes
    B = args.B # number of images per class
    flag = args.flag  # 1: gaussian bump ; 2: GRF ; 3: NS

    if flag == 1:
        ### GRF data ###
        ### load data
        data_name = f'data/GRF_train_K{K}_B{B}.npy'
        with open(data_name, 'rb') as f:
            c = np.load(f)

    elif flag == 2:
        ### NS data ###
        ### load data
        data_name = f"data/NS_train_K{K}_B{B}.npy"
        with open(data_name, 'rb') as f:
            c = np.load(f)

    elif flag == 3:
        ### era5 data ###
        c = np.memmap('data/era5_train_128x128_f32.npy', 
                       dtype=np.float32, 
                       mode='r', 
                       shape=(135, 2000, 128, 128))
        c = c.astype(np.float32)  # already in [0, 1]
        print(f"Loaded era5 data with shape: {c.shape}")


    elif flag == 4:
        ### sketch data ###
        data_name = f'data/sketch_150x2000x64x64.npy'
        with open(data_name, 'rb') as f:    
            c = np.load(f)
        c = c.astype(np.float32)  # already in [0, 1]
        print(f"Loaded sketch data with shape: {c.shape}")

    elif flag == 5:
        ### food data ###
        data_name = f'data/food_101_101x1000x128x128x3.npy'
        with open(data_name, 'rb') as f:    
            c = np.load(f)
        c = c.astype(np.float32) / 255.0  # normalize to [0, 1]
        print(f"Loaded food data with shape: {c.shape}")



    if c.ndim == 4:
        c = make_image_meta(c)  # shape (Nc, B, Nx, Nx)
        c = c[..., None]        # shape (Nc, B, Nx, Nx, 1)

    
    if flag == 2:
        save_name = 'data/NS_KMEresults.npz'
    elif flag == 3:
        save_name = 'data/Era5_KMEresults.npz'
    elif flag == 4:
        save_name = 'data/Sketch_KMEresults.npz'
    elif flag == 5:
        save_name = 'data/Food_KMEresults.npz'

    train_gray_c = torch.from_numpy(c).float()[:, :500, ...]
    state = fit_kme_pca_state(train_gray_c, embedding_dim=64)

    # training embeddings: [K, embed_dim]
    embeddings = compute_kme_embeddings(state)  # [K, r]
    print(f"Training embeddings shape: {tuple(embeddings.shape)}")

    # Convert all tensors to numpy, keep scalars as-is, save as .npz
    save_dict = {}
    for k, v in state.items():
        if isinstance(v, torch.Tensor):
            save_dict[k] = v.cpu().numpy()
        else:
            save_dict[k] = np.array(v)   # scalar -> 0-d array
    save_dict['train_embeddings'] = embeddings.cpu().numpy()

    np.savez(save_name, **save_dict)
    print(f"Saved full KME state to: {save_name}")