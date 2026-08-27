# In-Context Score Operator Learning for Diffusion Models Demo

This project provides code for the paper: 
[Transformer-based In-Context Score Operator Learning for Diffusion Models].
We currently release the demo code Navier-Stokes equation
## 1. Requirements
NS data generation uses JAX-CFD. Training and inference use PyTorch.

```bash
pip install -r requirements.txt
```


## 2. Prepare dataset

```bash
python prepare_NS_data.py \
  --B <samples_per_class> \
  --Nx <spatial_resolution> \
  --K <number_of_training_classes> \
  --K_test <number_of_test_classes>
```

This writes:

```text
data/NS_train_K{K}_B{B}.npy
data/NS_test_low_K{K_test}_B{B}.npy
data/NS_test_mid_K{K_test}_B{B}.npy
data/NS_test_high_K{K_test}_B{B}.npy
figs/NS_samples.png
```

The array layout is `(K, B, Nx, Nx)`: viscosity class, sample within the
class, and two spatial axes.

## 3. Train ICL-DM

NS is selected by `--flag 2`:

```bash
python train.py \
  --K <K> --B <B> --n <number_of_prompts> --nx <Nx> \
  --bs <batch_size> --flag 2 --epoch <epochs> \
  --num_prompts <number_of_prompt_sets> --idx <visualization_class>
```

The original script writes logs to `logs/`, figures to `figs/`, and a model
checkpoint to `mdls/` every 25 epochs.

## 4. Optional comparison models

Conditional-DM uses the same image-prompt dataset:

```bash
python train_cond.py \
  --K <K> --B <B> --n <number_of_prompts> --nx <Nx> \
  --bs <batch_size> --flag 2 --epoch <epochs> \
  --num_prompts <number_of_prompt_sets> --idx <visualization_class>
```

SNO first needs KME embeddings:

```bash
python prepare_KME_for_all.py --K <K> --B <B> --flag 2
```

The existing KME code uses at most the first 500 samples from every class and
writes `data/NS_KMEresults.npz`. It stores the flattened training samples as
well as the embeddings, so this file can be several GiB for a full run.

Then train SNO:

```bash
python train_SNO.py \
  --K <K> --B <B> --n <number_of_prompts> --nx <Nx> \
  --bs <batch_size> --flag 2 --epoch <epochs> \
  --num_prompts <number_of_prompt_sets> --idx <visualization_class>
```

## 5. Inference

`IND_NS.py` compares ICL-DM, Conditional-DM, and SNO, so all three matching
checkpoints and `data/NS_KMEresults.npz` must exist:

```bash
python IND_NS.py \
  --K <K> --B <B> --n <training_prompts> --m <inference_prompts> \
  --nx <Nx> --bs <batch_size> --epoch <checkpoint_epoch> \
  --np <number_of_prompt_sets> --idx <class_index>
```

Checkpoint names are constructed directly from these arguments. The dataset,
prompt count, prompt-set count, and epoch therefore need to match training.

