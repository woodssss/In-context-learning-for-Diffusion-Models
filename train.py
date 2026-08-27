import os
import functools
import torch
from torch.optim import Adam
from tqdm import tqdm
import matplotlib.pyplot as plt
import os
from torch.utils.data import DataLoader, TensorDataset
import argparse
from Net.TransUNet_small import TransUNet_small
from config.model_config_vpsde import *
import matplotlib.pyplot as plt
from matplotlib import cm
from utils.data_utils import gen_dataset_one, gen_GRF_dataset_one, generate_ns_image
from utils.utils import make_image, make_image_meta
from utils.train_ICL_utils import loss_score_t, ode_solver, loss_score_t_prompts
from functools import partial
import jax
import jax.numpy as jnp

device = torch.device("cuda" if torch.cuda.is_available() else
                      "cpu")

if torch.cuda.is_available():
    print(f"[INFO] Using GPU: {torch.cuda.get_device_name(0)}")
else:
    print("[INFO] Using CPU")

np.random.seed(42)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Generate Gaussian image dataset')
    parser.add_argument('--K', type=int, default=100, help='Number of classes')
    parser.add_argument('--B', type=int, default=1000, help='Number of images per class')
    parser.add_argument('--n', type=int, default=10, help='number of prompt images for training')
    parser.add_argument('--nx', type=int, default=64, help='number of prompt images for training')
    parser.add_argument('--bs', type=int, default=32, help='batch size for training')
    parser.add_argument('--flag', type=int, default=1, help='problem type')
    parser.add_argument('--epoch', type=int, default=200, help='epoch number')
    parser.add_argument('--num_prompts', type=int, default=1, help='number of prompts set')
    parser.add_argument('--idx', type=int, default=0, help='class index for testing/visualization')
    args = parser.parse_args()

    Nx = args.nx
    points_x_0 = np.linspace(0, 1, Nx)
    xx_0, yy_0 = np.meshgrid(points_x_0, points_x_0)

    sde = 'vp'

    K = args.K  # number of classes
    B = args.B # number of images per class
    n = args.n # number of images used for prompt in training
    m = n # number of images used for prompt in testing
    batch_size = args.bs
    num_prompts = args.num_prompts
    vis_idx = args.idx  # class index used for visualization

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
    elif flag == 6:
        ### dfaust data ###
        data_name = f'data/DFaust_class_100_nx_128_N_2000_train.npy'
        with open(data_name, 'rb') as f:    
            c = np.load(f)
        c = c.astype(np.float32)  # already in [0, 1]
        print(f"Loaded dfaust data with shape: {c.shape}")
    elif flag == 7:
        ### dfaust data ###
        data_name = f'data/DFaust_class_50_nx_128_N_4000_train.npy'
        with open(data_name, 'rb') as f:    
            c = np.load(f)
        c = c.astype(np.float32)  # already in [0, 1]
        print(f"Loaded dfaust data with shape: {c.shape}")


    if c.ndim == 4:
        c = make_image_meta(c)  # shape (Nc, B, Nx, Nx)
        c = c[..., None]        # shape (Nc, B, Nx, Nx, 1)

    # print(c.shape)

    # ### test and plot the dataset ###
    # bs = 5
    # fig1, ax = plt.subplots(1, bs, figsize=(bs * 2, 2))
    # for i in range(bs):
    #     ax[i].imshow(c[0, i, ...])
    # plt.show()
    # zxc
    # ###########################

    ### define model
    if flag == 5:
        model = TransUNet_small(in_ch=3, out_ch= 3, base_ch=128, heads=4, mul_ls=[1,2,4,8], n_cross_per_level=1).to(device)
    elif flag == 1 or flag == 2 or flag == 3 or flag == 4 or flag == 6:
        model = TransUNet_small(base_ch=64, heads=4, mul_ls=[1,2,4,8], n_cross_per_level=1).to(device)
    elif flag == 7:
        model = TransUNet_small(base_ch=128, heads=4, mul_ls=[1,2,4], n_cross_per_level=1).to(device)


    if flag == 1:
        save_name = 'GRF_Gen_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 2:
        save_name = 'NS_Gen_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 3:
        save_name = 'Era5_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 4:
        save_name = 'Sketch_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 5:
        save_name = 'Food_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 6:
        save_name = 'Dfaust_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)
    elif flag == 7:
        save_name = 'Dfaust_K_' + str(K) + '_B_' + str(B) + '_n_' + str(n) + '_np_' + str(num_prompts)

    train = torch.from_numpy(c).float()

    ### define training detail
    log_freq = 25
    batch_size = batch_size
    n_epochs = args.epoch + 1

    my_loss_func = loss_score_t

    total_params = sum(p.numel() for p in model.parameters())

    cwd = os.getcwd()

    log_name = cwd + '/logs/' + save_name + '_log.txt'
    chkpts_base_name = cwd + '/mdls/' + save_name

    optimizer = Adam(model.parameters(), lr=2e-4)
    scheduler = torch.optim.lr_scheduler.StepLR(optimizer, step_size=1000, gamma=0.9)

    print('[INFO] Starting training for model: %s' % (save_name))
    for epoch in tqdm(range(n_epochs)):
        avg_loss = 0.
        num_items = 0
        model.train()
        ### run over all the classes ###
        class_order = torch.randperm(K)
        for i in class_order:
            # ### randomly select n images from the class as prompts ###
            # idxs_prompt = np.random.choice(B, n, replace=False)
            # prompts = train[i, idxs_prompt, ...].to(device)

            ### randomly select images from the same class as training data ###
            tmp_dataset = TensorDataset(train[i, ...])
            tmp_data_loader = DataLoader(tmp_dataset, batch_size=batch_size, shuffle=True)

            for x in tmp_data_loader:
                # ### randomly select [n/2, n] images from the class as prompts ###
                # tmp_n = np.random.randint(n//2, n)
                # idxs_prompt = np.random.choice(B, tmp_n, replace=False)
                # prompts = train[i, idxs_prompt, ...].to(device)

                # x = x[0].to(device)
                # loss = my_loss_func(model, prompts, x, marginal_prob_fn)

                if num_prompts > 1:
                    prompts_ls = []
                    for kk in range(num_prompts):
                        ### randomly select [n/2, n] images from the class as prompts ###
                        tmp_n = n
                        idxs_prompt = np.random.choice(B, tmp_n, replace=False)
                        prompts = train[i, idxs_prompt, ...].to(device)
                        prompts_ls.append(prompts)

                    x = x[0].to(device)
                    loss = loss_score_t_prompts(model, prompts_ls, x, marginal_prob_fn)
                else:
                    ### randomly select [n/2, n] images from the class as prompts ###
                    tmp_n = n
                    idxs_prompt = np.random.choice(B, tmp_n, replace=False)
                    prompts = train[i, idxs_prompt, ...].to(device)

                    x = x[0].to(device)
                    loss = my_loss_func(model, prompts, x, marginal_prob_fn)

                

                optimizer.zero_grad()
                loss.backward()
                optimizer.step()
                scheduler.step()

                avg_loss += loss.item() * x.shape[0]
                num_items += x.shape[0]

        if epoch % log_freq == 0 and epoch > 0:
            content = 'at epoch: %d, Average Loss: %3f' % (
                epoch, avg_loss / num_items)
            mylogger(log_name, content)
            print(content)

            ############## plot results ############
            bs = 5
            idxs_prompt = np.random.choice(B, n, replace=False)
            prompts = train[vis_idx, idxs_prompt, ...].to(device)

            mat = train[vis_idx, :bs, ...]
            noise = torch.randn_like(mat).to(device)
            #noise = torch.randn(bs, Nx, Nx, 1).to(device)
            t = torch.ones(bs, device=device)

            model.eval()
            sample_f = ode_solver(model, marginal_prob_fn, get_sde_forward_fn, noise, prompts, forward=2, eps=1e-5, use_em=True, num_steps=1000)

            fig1, ax = plt.subplots(3, bs, figsize=(bs * 2, 6))

            def to_img(t):
                """Convert tensor [H,W,1] or [H,W,3] to numpy for imshow."""
                arr = t.detach().cpu().numpy()
                if arr.ndim == 3 and arr.shape[-1] == 1:
                    arr = arr[..., 0]
                arr = np.clip(arr, 0, 1) if arr.max() <= 1.5 else arr
                return arr

            for j in range(bs):
                if j < prompts.shape[0]:
                    ax[0, j].imshow(to_img(prompts[j]))
                ax[0, j].axis("off")
                ax[1, j].imshow(to_img(sample_f[j]))
                ax[1, j].axis("off")
                ax[2, j].imshow(to_img(mat[j]))
                ax[2, j].axis("off")
            ax[0, 0].set_ylabel('Prompts', fontsize=8)
            ax[1, 0].set_ylabel('Generated', fontsize=8)
            ax[2, 0].set_ylabel('Ground Truth', fontsize=8)
            plt.tight_layout()
            
            # Save figure
            fig_path = cwd + '/figs/' + save_name + '_idx_' + str(vis_idx) + '_epoch_' + str(epoch) + '.png'
            plt.savefig(fig_path, dpi=150, bbox_inches='tight')
            print(f"Saved figure to {fig_path}")
            plt.close()

            chkpts_model_name = chkpts_base_name + '_epoch_' + str(epoch) + '_ckpt.pt'
            torch.save(model, chkpts_model_name)