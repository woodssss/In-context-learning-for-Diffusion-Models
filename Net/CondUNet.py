import math
from typing import List, Optional

import torch
import torch.nn as nn
import torch.nn.functional as F


# =========================================================
# 1) Timestep embedding
# =========================================================
def get_timestep_embedding(t: torch.Tensor, dim: int) -> torch.Tensor:
    """
    t: [B] integer/float timesteps
    returns: [B, dim]
    """
    half = dim // 2
    freqs = torch.exp(
        -math.log(10000.0) * torch.arange(0, half, dtype=torch.float32, device=t.device) / max(half - 1, 1)
    )
    args = t.float()[:, None] * freqs[None, :]
    emb = torch.cat([torch.cos(args), torch.sin(args)], dim=1)
    if dim % 2 == 1:
        emb = torch.cat([emb, torch.zeros_like(emb[:, :1])], dim=1)
    return emb


# =========================================================
# 2) Basic blocks
# =========================================================
class ResBlock(nn.Module):
    """
    FiLM-style conditioning via temb:
      GN -> (1+scale)*h + shift
    """
    def __init__(self, in_ch: int, out_ch: int, temb_dim: int, groups: int = 4, dropout: float = 0.1):
        super().__init__()
        self.norm1 = nn.GroupNorm(groups, in_ch)
        self.act1 = nn.SiLU()
        self.conv1 = nn.Conv2d(in_ch, out_ch, 3, padding=1)

        self.temb_proj = nn.Sequential(
            nn.SiLU(),
            nn.Linear(temb_dim, 2 * out_ch),
        )

        self.norm2 = nn.GroupNorm(groups, out_ch)
        self.act2 = nn.SiLU()
        self.dropout = nn.Dropout(dropout)
        self.conv2 = nn.Conv2d(out_ch, out_ch, 3, padding=1)

        self.skip = nn.Identity() if in_ch == out_ch else nn.Conv2d(in_ch, out_ch, 1)

    def forward(self, x: torch.Tensor, temb: torch.Tensor) -> torch.Tensor:
        h = self.conv1(self.act1(self.norm1(x)))

        ss = self.temb_proj(temb)  # [B, 2*out_ch]
        scale, shift = ss.chunk(2, dim=1)
        scale = scale[:, :, None, None]
        shift = shift[:, :, None, None]

        h = self.norm2(h)
        h = h * (1.0 + scale) + shift
        h = self.conv2(self.dropout(self.act2(h)))

        return h + self.skip(x)


class Downsample(nn.Module):
    def __init__(self, in_ch: int, out_ch: int):
        super().__init__()
        self.conv = nn.Conv2d(in_ch, out_ch, 3, stride=2, padding=1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.conv(x)


class Upsample(nn.Module):
    def __init__(self, in_ch: int, out_ch: int):
        super().__init__()
        self.conv = nn.Conv2d(in_ch, out_ch, 3, padding=1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        x = F.interpolate(x, scale_factor=2.0, mode="nearest")
        return self.conv(x)


# =========================================================
# 3) Self-attention (NO cross-attn, NO KV)
# =========================================================
class SelfAttention2D(nn.Module):
    """
    Standard 2D self-attention over spatial positions.
    x: [B,C,H,W] -> x + Attn(x)
    """
    def __init__(self, channels: int, num_heads: int = 4, groups: int = 4):
        super().__init__()
        assert channels % num_heads == 0, "channels must be divisible by num_heads"
        self.channels = channels
        self.num_heads = num_heads
        self.head_dim = channels // num_heads

        self.norm = nn.GroupNorm(groups, channels)
        self.qkv = nn.Conv2d(channels, 3 * channels, 1)
        self.proj = nn.Conv2d(channels, channels, 1)

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        B, C, H, W = x.shape
        h = self.norm(x)
        qkv = self.qkv(h)
        q, k, v = qkv.chunk(3, dim=1)

        # reshape
        # q: [B, heads, HW, head_dim]
        q = q.view(B, self.num_heads, self.head_dim, H * W).permute(0, 1, 3, 2)
        # k: [B, heads, head_dim, HW]
        k = k.view(B, self.num_heads, self.head_dim, H * W)
        # v: [B, heads, HW, head_dim]
        v = v.view(B, self.num_heads, self.head_dim, H * W).permute(0, 1, 3, 2)

        attn = torch.matmul(q, k) * (self.head_dim ** -0.5)  # [B, heads, HW, HW]
        attn = attn.softmax(dim=-1)

        out = torch.matmul(attn, v)  # [B, heads, HW, head_dim]
        out = out.permute(0, 1, 3, 2).contiguous().view(B, C, H, W)
        out = self.proj(out)
        return x + out


# =========================================================
# 4) Prompt -> vector latent (deepest only)
#    - mean over N (set pooling)
#    - learned spatial attention pooling (NOT mean over H,W)
# =========================================================
class SpatialAttnPool(nn.Module):
    """
    Learned pooling over spatial positions.
    Input:  x [B,C,H,W] or [C,H,W]
    Output: v [B,C] or [C]
    """
    def __init__(self, C: int, hidden: int = 128):
        super().__init__()
        self.score = nn.Sequential(
            nn.Linear(C, hidden),
            nn.SiLU(),
            nn.Linear(hidden, 1),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        squeeze_back = False
        if x.dim() == 3:
            x = x.unsqueeze(0)
            squeeze_back = True

        B, C, H, W = x.shape
        tokens = x.permute(0, 2, 3, 1).reshape(B, H * W, C)  # [B, HW, C]
        logits = self.score(tokens).squeeze(-1)              # [B, HW]
        w = logits.softmax(dim=1).unsqueeze(-1)              # [B, HW, 1]
        v = (tokens * w).sum(dim=1)                          # [B, C]

        if squeeze_back:
            v = v.squeeze(0)
        return v


class PromptEncoderDeep(nn.Module):
    """
    Returns ONLY the deepest feature map for the prompt set.
    No intermediate prompt features are stored/returned.

    Input:
      f_set: [N,H,W,1] or [N,1,H,W]
    Output:
      deep:  [N, Cdeep, h, w]
    """
    def __init__(
        self,
        in_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        mul_ls: List[int] = [1, 2, 4],
        use_self_attn_at_deepest: bool = True,
        attn_heads: int = 4,
    ):
        super().__init__()
        self.base_ch = base_ch
        self.mul_ls = mul_ls

        # No conditioning inside prompt encoder
        temb_dim = base_ch * 4  # dummy for ResBlock signature; we will pass zeros
        self.zero_temb = None

        self.conv_in = nn.Conv2d(in_ch, base_ch, 3, 1, 1)
        self.initial_down = Downsample(base_ch, base_ch)

        self.encoders = nn.ModuleList()
        self.downs = nn.ModuleList()

        for i, mul in enumerate(mul_ls):
            ch = base_ch * mul
            if i == 0:
                self.encoders.append(ResBlock(base_ch, ch, temb_dim, groups, dropout))
            else:
                self.encoders.append(ResBlock(ch, ch, temb_dim, groups, dropout))

            if i < len(mul_ls) - 1:
                next_ch = base_ch * mul_ls[i + 1]
                self.downs.append(Downsample(ch, next_ch))

        deep_ch = base_ch * mul_ls[-1]
        self.use_self_attn_at_deepest = use_self_attn_at_deepest
        self.deep_attn = SelfAttention2D(deep_ch, num_heads=attn_heads, groups=groups) if use_self_attn_at_deepest else None

        # constant zero temb for prompt encoder (since it is unconditional)
        self._temb_dim = temb_dim

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        if x.dim() == 4 and x.shape[1] != 1:
            x = x.permute(0, 3, 1, 2)  # [N,1,H,W]

        N = x.shape[0]
        # build a zero temb so ResBlocks work without changing their code
        temb0 = torch.zeros((N, self._temb_dim), device=x.device, dtype=x.dtype)

        h = self.conv_in(x)
        h = self.initial_down(h)

        for i, enc in enumerate(self.encoders):
            h = enc(h, temb0)
            if i < len(self.downs):
                h = self.downs[i](h)

        if self.deep_attn is not None:
            h = self.deep_attn(h)

        return h  # [N, Cdeep, h, w]


class PromptSetToTemb(nn.Module):
    """
    f_set -> prompt temb vector [B, temb_dim]
    - Uses deepest prompt feature only
    - Mean over N
    - Learned attention pooling over H*W
    """
    def __init__(
        self,
        in_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        mul_ls: List[int] = [1, 2, 4],
        pool_hidden: int = 128,
        prompt_attn_heads: int = 4,
        prompt_use_self_attn: bool = True,
    ):
        super().__init__()
        self.temb_dim = base_ch * 4
        self.prompt_encoder = PromptEncoderDeep(
            in_ch=in_ch,
            base_ch=base_ch,
            groups=groups,
            dropout=dropout,
            mul_ls=mul_ls,
            use_self_attn_at_deepest=prompt_use_self_attn,
            attn_heads=prompt_attn_heads,
        )

        deep_C = base_ch * mul_ls[-1]
        self.spatial_pool = SpatialAttnPool(deep_C, hidden=pool_hidden)
        self.prompt_proj = nn.Sequential(
            nn.Linear(deep_C, self.temb_dim),
            nn.SiLU(),
            nn.Linear(self.temb_dim, self.temb_dim),
        )

    def forward(self, f_set: torch.Tensor, B: int) -> torch.Tensor:
        # shared prompt: [N,H,W,1] or [N,1,H,W]
        if f_set.dim() == 4:
            deep = self.prompt_encoder(f_set)  # [N,C,h,w]
            deep = deep.mean(dim=0)            # [C,h,w]  (mean over N)
            v = self.spatial_pool(deep)        # [C]      (learned pool over HW)
            temb_p = self.prompt_proj(v)       # [temb_dim]
            return temb_p.unsqueeze(0).expand(B, -1)

        # per-sample prompt: [B,N,H,W,1] or [B,N,1,H,W]
        if f_set.dim() == 5:
            B2, N = f_set.shape[0], f_set.shape[1]
            assert B2 == B, "If f_set is [B,N,...], B must match x_t batch size."
            x = f_set.reshape(B * N, *f_set.shape[2:])  # [B*N,...]
            deep = self.prompt_encoder(x)               # [B*N,C,h,w]
            deep = deep.reshape(B, N, *deep.shape[1:])  # [B,N,C,h,w]
            deep = deep.mean(dim=1)                     # [B,C,h,w]
            v = self.spatial_pool(deep)                 # [B,C]
            temb_p = self.prompt_proj(v)                # [B,temb_dim]
            return temb_p

        raise ValueError(f"Unsupported f_set shape: {tuple(f_set.shape)}")


# =========================================================
# 5) UNet: prompt is vector, injected exactly like t (addition into temb)
#    + optional self-attn at the bottleneck (deepest UNet)
# =========================================================
class MultiResUNetPromptVector(nn.Module):
    def __init__(
        self,
        in_ch: int = 1,
        out_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        mul_ls: List[int] = [1, 2, 4],
        use_self_attn_mid: bool = True,
        attn_heads: int = 4,
    ):
        super().__init__()
        self.base_ch = base_ch
        self.temb_dim = base_ch * 4
        self.mul_ls = mul_ls

        self.time_proj = nn.Sequential(
            nn.Linear(base_ch, self.temb_dim),
            nn.SiLU(),
            nn.Linear(self.temb_dim, self.temb_dim),
        )

        self.conv_in = nn.Conv2d(in_ch, base_ch, 3, 1, 1)
        self.initial_down = Downsample(base_ch, base_ch)

        # encoder
        self.encoders = nn.ModuleList()
        self.downs = nn.ModuleList()

        for i, mul in enumerate(mul_ls):
            ch = base_ch * mul
            if i == 0:
                self.encoders.append(ResBlock(base_ch, ch, self.temb_dim, groups, dropout))
            else:
                self.encoders.append(ResBlock(ch, ch, self.temb_dim, groups, dropout))
            if i < len(mul_ls) - 1:
                next_ch = base_ch * mul_ls[i + 1]
                self.downs.append(Downsample(ch, next_ch))

        # self-attn at bottleneck (deepest UNet)
        deep_ch = base_ch * mul_ls[-1]
        self.mid_attn = SelfAttention2D(deep_ch, num_heads=attn_heads, groups=groups) if use_self_attn_mid else None

        # decoder
        self.ups = nn.ModuleList()
        self.decoders = nn.ModuleList()
        for i in range(len(mul_ls) - 2, -1, -1):
            ch = base_ch * mul_ls[i]
            next_ch = base_ch * mul_ls[i + 1]
            self.ups.append(Upsample(next_ch, ch))
            self.decoders.append(ResBlock(ch * 2, ch, self.temb_dim, groups, dropout))

        final_ch = base_ch * mul_ls[0]
        self.final_up = Upsample(final_ch, final_ch)
        self.final = nn.Sequential(
            nn.GroupNorm(groups, final_ch),
            nn.SiLU(),
            nn.Conv2d(final_ch, out_ch, 3, 1, 1),
        )

    def forward(self, x: torch.Tensor, t: torch.Tensor, prompt_temb: torch.Tensor) -> torch.Tensor:
        """
        x: [B,H,W,1] or [B,1,H,W]
        t: [B]
        prompt_temb: [B, temb_dim]
        """
        if x.dim() == 4 and x.shape[1] != 1:
            x = x.permute(0, 3, 1, 2)
        B = x.shape[0]

        t_emb = get_timestep_embedding(t, self.base_ch)  # [B, base_ch]
        t_emb = self.time_proj(t_emb)                    # [B, temb_dim]
        temb = t_emb + prompt_temb                       # prompt injected EXACTLY like t

        h = self.conv_in(x)
        h = self.initial_down(h)

        skips = []
        for i, enc in enumerate(self.encoders):
            h = enc(h, temb)
            skips.append(h)
            if i < len(self.downs):
                h = self.downs[i](h)

        if self.mid_attn is not None:
            h = self.mid_attn(h)

        for i, (up, dec) in enumerate(zip(self.ups, self.decoders)):
            h = up(h)
            skip = skips[len(skips) - 2 - i]
            h = torch.cat([h, skip], dim=1)
            h = dec(h, temb)

        h = self.final_up(h)
        out = self.final(h)
        return out.permute(0, 2, 3, 1)


# =========================================================
# 6) Full model
# =========================================================
class CondUNet(nn.Module):
    """
    Inputs:
      f_set: [N,H,W,1] shared prompt OR [B,N,H,W,1] per-sample prompt
      x_t:   [B,H,W,1]
      t:     [B]

    Output:
      eps:   [B,H,W,1]
    """
    def __init__(
        self,
        in_ch: int = 1,
        out_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        mul_ls: List[int] = [1, 2, 4],
        pool_hidden: int = 128,
        # self-attn configs
        unet_use_self_attn_mid: bool = True,
        unet_attn_heads: int = 4,
        prompt_use_self_attn: bool = True,
        prompt_attn_heads: int = 4,
    ):
        super().__init__()
        self.prompt_to_temb = PromptSetToTemb(
            in_ch=in_ch,
            base_ch=base_ch,
            groups=groups,
            dropout=dropout,
            mul_ls=mul_ls,
            pool_hidden=pool_hidden,
            prompt_attn_heads=prompt_attn_heads,
            prompt_use_self_attn=prompt_use_self_attn,
        )

        self.unet = MultiResUNetPromptVector(
            in_ch=in_ch,
            out_ch=out_ch,
            base_ch=base_ch,
            groups=groups,
            dropout=dropout,
            mul_ls=mul_ls,
            use_self_attn_mid=unet_use_self_attn_mid,
            attn_heads=unet_attn_heads,
        )

    def forward(self, f_set: torch.Tensor, x_t: torch.Tensor, t: torch.Tensor) -> torch.Tensor:
        B = x_t.shape[0]
        prompt_temb = self.prompt_to_temb(f_set, B=B)  # [B, temb_dim]
        return self.unet(x_t, t, prompt_temb)