from utils.data_utils import generate_ns_image
import numpy as np
from tqdm import tqdm
import argparse
from utils.utils import make_image_meta

parser = argparse.ArgumentParser(description='Prepare NS dataset')
parser.add_argument('--B', type=int, default=5, help='Number of images per class')
parser.add_argument('--Nx', type=int, default=128, help='Image size')
parser.add_argument('--K', type=int, default=10, help='Number of classes')
parser.add_argument('--K_test', type=int, default=3, help='Number of test classes')
args = parser.parse_args()

B = args.B
Nx = args.Nx
K = args.K
K_test = args.K_test

### prepare for training: K/2 classes uniform in [1.5e-3, 1e-2], K/2 classes uniform in [2e-2, 6e-2]
K1 = K // 2
K2 = K - K1
nu_seg1 = [1.5e-3 + (1e-2 - 1.5e-3) / (K1 - 1) * i for i in range(K1)]  # K1 values in [1.5e-3, 1e-2]
nu_seg2 = [2e-2  + (6e-2 - 2e-2)   / (K2 - 1) * i for i in range(K2)]  # K2 values in [2e-2, 6e-2]
nu_list  = nu_seg1 + nu_seg2  # length K

ls = [generate_ns_image(N=B, size=Nx, seed=i, nu_range=nu_list[i]) for i in tqdm(range(K))]
train_data = np.stack(ls, axis=0)  # shape (K, B, Nx, Nx)
train_data = make_image_meta(train_data)


######### out of distribution test data #########
### prepare for testing 1: nu [1e-2, 2e-2]
ls_test_1 = [generate_ns_image(N=B, size=Nx, seed=i, nu_range=1e-2 + (2e-2 - 1e-2)/K_test * i) for i in tqdm(range(K_test))]
test_data_mid = np.stack(ls_test_1, axis=0)  # shape (K_test, B, Nx, Nx)
test_data_mid = make_image_meta(test_data_mid)

### prepare for testing 2: nu [1e-3, 1.5e-3]
ls_test_2 = [generate_ns_image(N=B, size=Nx, seed=i, nu_range=1e-3 + (1.5e-3 - 1e-3)/K_test * i) for i in tqdm(range(K_test))]
test_data_low = np.stack(ls_test_2, axis=0)  # shape (K_test, B, Nx, Nx)
test_data_low = make_image_meta(test_data_low)

### prepare for testing 3: nu [6e-2, 7e-2]
ls_test_3 = [generate_ns_image(N=B, size=Nx, seed=i, nu_range=6e-2 + (7e-2 - 6e-2)/K_test * i) for i in tqdm(range(K_test))]
test_data_high = np.stack(ls_test_3, axis=0)  # shape (K_test, B, Nx, Nx)
test_data_high = make_image_meta(test_data_high)

### save data
np.save(f'data/NS_train_K{K}_B{B}.npy', train_data)
np.save(f'data/NS_test_mid_K{K_test}_B{B}.npy', test_data_mid)
np.save(f'data/NS_test_low_K{K_test}_B{B}.npy', test_data_low)
np.save(f'data/NS_test_high_K{K_test}_B{B}.npy', test_data_high)
print("Saved train and test data to data/")

### plot samples
import matplotlib.pyplot as plt

ncols = 10
labels = ['Train ν∈[1.5e-3,1e-2]∪[2e-2,6e-2]', 'Test1 ν∈[1e-2,2e-2]', 'Test2 ν∈[1e-3,1.5e-3]', 'Test3 ν∈[6e-2,7e-2]']
datasets = [train_data, test_data_mid, test_data_low, test_data_high]

fig, axes = plt.subplots(4, ncols, figsize=(ncols * 1.5, 4 * 1.5))
for row, (data, label) in enumerate(zip(datasets, labels)):
    idx = np.random.choice(data.shape[0] * data.shape[1], ncols, replace=False)
    for col, i in enumerate(idx):
        k, b = divmod(i, data.shape[1])
        axes[row, col].imshow(data[k, b], cmap='RdBu_r')
        axes[row, col].axis('off')
    axes[row, 0].set_ylabel(label, fontsize=8, rotation=90, labelpad=4)

plt.tight_layout()
plt.savefig('figs/NS_samples.png', dpi=150, bbox_inches='tight')
print("Saved plot to figs/NS_samples.png")

