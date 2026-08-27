import math
from typing import List

import torch
import torch.nn as nn
import torch.nn.functional as F


# ---------------------------------------------------------
# 1) Timestep embedding
# ---------------------------------------------------------

def get_timestep_embedding(t: torch.Tensor, dim: int) -> torch.Tensor:
    """
    Sinusoidal timestep embedding.
    t:   [B]
    dim: embedding dimension
    returns: [B, dim]
    """
    device = t.device
    half = dim // 2
    freqs = torch.exp(-math.log(10000) * torch.arange(half, device=device) / half)
    args = t[:, None] * freqs[None, :]
    emb = torch.cat([torch.sin(args), torch.cos(args)], dim=-1)
    if dim % 2 == 1:
        emb = F.pad(emb, (0, 1))
    return emb


# ---------------------------------------------------------
# 2) ResBlock with (optional) time FiLM, SiLU, GroupNorm
# ---------------------------------------------------------

class ResBlock(nn.Module):
    def __init__(
        self,
        in_ch: int,
        out_ch: int,
        temb_dim: int,
        groups: int = 4,
        dropout: float = 0.1,
    ):
        super().__init__()
        self.in_ch = in_ch
        self.out_ch = out_ch

        self.norm1 = nn.GroupNorm(groups, in_ch)
        self.act1 = nn.SiLU()
        self.conv1 = nn.Conv2d(in_ch, out_ch, 3, padding=1)

        self.norm2 = nn.GroupNorm(groups, out_ch)
        self.act2 = nn.SiLU()
        self.dropout = nn.Dropout(dropout)
        self.conv2 = nn.Conv2d(out_ch, out_ch, 3, padding=1)

        # time embedding → FiLM (scale + shift)
        self.use_temb = temb_dim > 0
        if self.use_temb:
            self.temb_proj = nn.Linear(temb_dim, out_ch * 2)

        # shortcut
        if in_ch == out_ch:
            self.shortcut = nn.Identity()
        else:
            self.shortcut = nn.Conv2d(in_ch, out_ch, 1)

    def forward(self, x, temb):
        """
        x:    [B, C_in, H, W]
        temb: [B, temb_dim] or None
        """
        h = self.conv1(self.act1(self.norm1(x)))

        if self.use_temb and temb is not None:
            temb_out = self.temb_proj(temb)  # [B, 2*out_ch]
            scale, shift = temb_out.chunk(2, dim=1)
            scale = scale[:, :, None, None]
            shift = shift[:, :, None, None]
            h = h * (1 + scale) + shift

        h = self.conv2(self.dropout(self.act2(self.norm2(h))))
        return h + self.shortcut(x)


# ---------------------------------------------------------
# 3) Downsample / Upsample
# ---------------------------------------------------------

class Downsample(nn.Module):
    def __init__(self, in_ch: int, out_ch: int):
        super().__init__()
        self.conv = nn.Conv2d(in_ch, out_ch, 4, stride=2, padding=1)

    def forward(self, x):
        return self.conv(x)


class Upsample(nn.Module):
    def __init__(self, in_ch: int, out_ch: int):
        super().__init__()
        self.conv = nn.ConvTranspose2d(in_ch, out_ch, 4, stride=2, padding=1)

    def forward(self, x):
        return self.conv(x)


# ---------------------------------------------------------
# 4) Cross-attention on 2D maps (full resolution per scale)
# ---------------------------------------------------------

class CrossAttention2D(nn.Module):
    """
    Cross-attention between:
      q_feat:  [B, C, H, W]
      kv_feat: [C, H, W] (pooled over prompts)

    Performs:
      - flatten to [B, L, C], [B, L, C]
      - MultiheadAttention(Q, K, V)
      - residual + FFN
      - reshape back to [B, C, H, W]
    """

    def __init__(self, channels: int, heads: int = 8):
        super().__init__()
        self.channels = channels
        self.mha = nn.MultiheadAttention(channels, heads, batch_first=True)
        self.norm1 = nn.LayerNorm(channels)
        self.norm2 = nn.LayerNorm(channels)
        self.ff = nn.Sequential(
            nn.Linear(channels, 4 * channels),
            nn.SiLU(),
            nn.Linear(4 * channels, channels),
        )

    def forward(self, q_feat: torch.Tensor, kv_feat: torch.Tensor) -> torch.Tensor:
        """
        q_feat: [B, C, H, W]
        kv_feat: [C, H, W]
        """
        B, C, H, W = q_feat.shape
        L = H * W

        # flatten
        q = q_feat.view(B, C, L).transpose(1, 2)  # [B, L, C]
        kv = kv_feat.view(C, L).transpose(0, 1)   # [L, C]
        kv = kv.unsqueeze(0).expand(B, -1, -1)    # [B, L, C]

        # cross-attention
        h = self.norm1(q)
        attn_out, _ = self.mha(h, kv, kv)
        h = q + attn_out
        h = h + self.ff(self.norm2(h))

        # back to 2D
        h = h.transpose(1, 2).view(B, C, H, W)
        return h


# ---------------------------------------------------------
# 5) Prompt encoder UNet (for K,V at multiple resolutions)
#    MODIFIED: Downsamples FIRST, then processes
# ---------------------------------------------------------

# ---------------------------------------------------------
# 5a) Self-attention over the N prompts (set transformer layer)
# ---------------------------------------------------------

class PromptSetTransformer(nn.Module):
    """
    Applies multi-head self-attention over N prompt tokens at a given
    spatial resolution, allowing prompts to interact before pooling.

    Input:  x [N, C, H, W]
    Output: x [N, C, H, W]  (same shape)
    """
    def __init__(self, channels: int, heads: int = 4, groups: int = 4):
        super().__init__()
        assert channels % heads == 0
        self.heads = heads
        self.head_dim = channels // heads
        self.norm = nn.GroupNorm(groups, channels)
        self.to_qkv = nn.Linear(channels, 3 * channels)
        self.proj = nn.Linear(channels, channels)
        self.norm2 = nn.GroupNorm(groups, channels)
        self.ffn = nn.Sequential(
            nn.Linear(channels, channels * 2),
            nn.SiLU(),
            nn.Linear(channels * 2, channels),
        )

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        # x: [N, C, H, W]
        N, C, H, W = x.shape

        # spatial mean pool → token per prompt: [N, C]
        tokens = x.mean(dim=(-2, -1))                          # [N, C]
        tokens_norm = self.norm(tokens.unsqueeze(-1).unsqueeze(-1)).squeeze(-1).squeeze(-1)  # [N, C]

        # self-attention over N tokens
        qkv = self.to_qkv(tokens_norm)                        # [N, 3C]
        q, k, v = qkv.chunk(3, dim=-1)                        # each [N, C]

        q = q.view(N, self.heads, self.head_dim)               # [N, h, d]
        k = k.view(N, self.heads, self.head_dim)
        v = v.view(N, self.heads, self.head_dim)

        # attention: [h, N, N]
        attn = torch.einsum('nhd,mhd->hnm', q, k) * (self.head_dim ** -0.5)
        attn = attn.softmax(dim=-1)
        out = torch.einsum('hnm,mhd->nhd', attn, v)           # [N, h, d]
        out = out.reshape(N, C)                                 # [N, C]
        out = self.proj(out)

        tokens2 = tokens + out                                  # residual

        # FFN residual
        n2 = self.norm2(tokens2.unsqueeze(-1).unsqueeze(-1)).squeeze(-1).squeeze(-1)
        tokens2 = tokens2 + self.ffn(n2)

        # broadcast delta back to spatial map
        delta = (tokens2 - tokens)[:, :, None, None]           # [N, C, 1, 1]
        return x + delta


class PromptEncoderUNet(nn.Module):
    """
    Prompt encoder for f_set, WITH time dependence and set-level
    self-attention so prompts can interact before being pooled.

    MODIFIED: Downsamples input first to avoid OOM at highest resolution.

    Inputs:
      x:    [N, H, W, 1] or [N, 1, H, W]
      temb: [B, temb_dim]  -- time embedding (broadcast over N)

    Outputs:
      List of features at different resolutions based on mul_ls
    """

    def __init__(
        self,
        in_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        mul_ls: List[int] = [1, 2, 4],
        temb_dim: int = 0,
        heads: int = 4,
    ):
        super().__init__()
        self.mul_ls = mul_ls
        self.num_levels = len(mul_ls)
        self.temb_dim = temb_dim

        # Time embedding projection (if time is provided)
        if temb_dim > 0:
            self.time_proj = nn.Sequential(
                nn.Linear(base_ch, temb_dim),
                nn.SiLU(),
                nn.Linear(temb_dim, temb_dim),
            )
        else:
            self.time_proj = None

        # Initial convolution + downsample by 2 to start at H/2, W/2
        self.conv_in = nn.Conv2d(in_ch, base_ch, 3, 1, 1)
        self.initial_downsample = Downsample(base_ch, base_ch)  # H,W → H/2,W/2

        # Create encoder blocks, set-transformers and downsample layers
        self.encoders = nn.ModuleList()
        self.set_transformers = nn.ModuleList()   # self-attn over N prompts per level
        self.downsamplers = nn.ModuleList()

        for i, mul in enumerate(mul_ls):
            ch = base_ch * mul
            if i == 0:
                encoder = ResBlock(base_ch, ch, temb_dim, groups, dropout)
            else:
                encoder = ResBlock(ch, ch, temb_dim, groups, dropout)
            self.encoders.append(encoder)

            # self-attention over N prompts at this level
            self.set_transformers.append(PromptSetTransformer(ch, heads=heads, groups=groups))

            # Add downsampler (except for the last level)
            if i < len(mul_ls) - 1:
                next_ch = base_ch * mul_ls[i+1]
                downsampler = Downsample(ch, next_ch)
                self.downsamplers.append(downsampler)

    def forward(self, x, temb=None):
        """
        x:    [N, H, W, C] or [N, C, H, W]
        temb: [temb_dim] or None  -- broadcast time embedding
        Returns features at [H/2, H/4, H/8, ...] resolutions, each [N, ch, H_i, W_i]
        """
        if x.dim() == 4 and x.shape[-1] != x.shape[1]:
            # assume [N, H, W, C] → [N, C, H, W]
            x = x.permute(0, 3, 1, 2)

        h = self.conv_in(x)               # [N, base_ch, H, W]
        h = self.initial_downsample(h)    # [N, base_ch, H/2, W/2]

        # Broadcast temb over N prompts: [N, temb_dim]
        if temb is not None and self.time_proj is not None:
            N = h.shape[0]
            t_prompt = self.time_proj(temb)          # [temb_dim]
            t_prompt = t_prompt.unsqueeze(0).expand(N, -1)  # [N, temb_dim]
        else:
            t_prompt = None

        features = []
        for i, encoder in enumerate(self.encoders):
            h = encoder(h, t_prompt)                  # ResBlock with time conditioning
            h = self.set_transformers[i](h)           # self-attn over N prompts
            features.append(h)

            if i < len(self.downsamplers):
                h = self.downsamplers[i](h)

        return features


# ---------------------------------------------------------
# 6) Time-conditioned UNet with multi-res stacked cross-attention
#    MODIFIED: Downsamples FIRST, then processes
# ---------------------------------------------------------

class MultiResUNetCrossAttention(nn.Module):
    """
    Time-conditioned UNet for x_t with multi-resolution cross-attention
    against prompt features at multiple resolution levels specified by mul_ls.
    
    MODIFIED: Downsamples input first to avoid OOM at highest resolution.
    Works at H/2, H/4, H/8, ... resolutions, then upsamples back to H at the end.

    Cross-attention is stacked multiple times at each scale.
    """

    def __init__(
        self,
        in_ch: int = 1,
        out_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        heads: int = 8,
        mul_ls: List[int] = [1, 2, 4],
        n_cross_per_level: int = 2,
    ):
        super().__init__()
        self.base_ch = base_ch
        self.temb_dim = base_ch * 4
        self.mul_ls = mul_ls
        self.num_levels = len(mul_ls)

        # time embedding MLP: base_ch → 4*base_ch → 4*base_ch
        self.time_proj = nn.Sequential(
            nn.Linear(base_ch, self.temb_dim),
            nn.SiLU(),
            nn.Linear(self.temb_dim, self.temb_dim),
        )

        # Initial convolution + downsample by 2 to start at H/2, W/2
        self.conv_in = nn.Conv2d(in_ch, base_ch, 3, 1, 1)
        self.initial_downsample = Downsample(base_ch, base_ch)  # H,W → H/2,W/2

        # Encoder path
        self.encoders = nn.ModuleList()
        self.cross_encoders = nn.ModuleList()
        self.downsamplers = nn.ModuleList()
        
        for i, mul in enumerate(mul_ls):
            ch = base_ch * mul
            if i == 0:
                # First level uses base_ch input from initial_downsample
                encoder = ResBlock(base_ch, ch, self.temb_dim, groups, dropout)
            else:
                # Subsequent levels take input from previous downsampler
                encoder = ResBlock(ch, ch, self.temb_dim, groups, dropout)
            
            cross_attn = nn.ModuleList([
                CrossAttention2D(ch, heads) for _ in range(n_cross_per_level)
            ])
            
            self.encoders.append(encoder)
            self.cross_encoders.append(cross_attn)
            
            # Add downsampler (except for the last level)
            if i < len(mul_ls) - 1:
                next_ch = base_ch * mul_ls[i+1]
                downsampler = Downsample(ch, next_ch)
                self.downsamplers.append(downsampler)

        # Decoder path (reverse order)
        self.upsamplers = nn.ModuleList()
        self.decoders = nn.ModuleList()
        self.cross_decoders = nn.ModuleList()
        
        for i in range(len(mul_ls) - 2, -1, -1):  # Skip the deepest level, go from second-to-last to first
            mul = mul_ls[i]
            next_mul = mul_ls[i + 1]
            ch = base_ch * mul
            next_ch = base_ch * next_mul
            
            # Upsampler
            upsampler = Upsample(next_ch, ch)
            
            # Decoder takes concatenated input (upsampled + skip connection)
            decoder = ResBlock(ch * 2, ch, self.temb_dim, groups, dropout)
            
            # Cross attention
            cross_attn = nn.ModuleList([
                CrossAttention2D(ch, heads) for _ in range(n_cross_per_level)
            ])
            
            self.upsamplers.append(upsampler)
            self.decoders.append(decoder)
            self.cross_decoders.append(cross_attn)

        # Final upsampling back to original resolution + projection
        final_ch = base_ch * mul_ls[0]
        self.final_upsample = Upsample(final_ch, final_ch)  # H/2,W/2 → H,W
        self.final = nn.Sequential(
            nn.GroupNorm(groups, final_ch),
            nn.SiLU(),
            nn.Conv2d(final_ch, out_ch, 3, 1, 1),
        )

    def forward(
        self,
        x: torch.Tensor,
        t: torch.Tensor,
        kv_features: List[torch.Tensor],
    ) -> torch.Tensor:
        """
        x:           [B, H, W, 1] or [B, 1, H, W]
        t:           [B]
        kv_features: List of [base_ch * mul_ls[i], H/(2^(i+1)), W/(2^(i+1))] tensors
        """
        if x.dim() == 4 and x.shape[1] != 1:
            x = x.permute(0, 3, 1, 2)  # [B,1,H,W]

        # time embedding
        t_emb = get_timestep_embedding(t, self.base_ch)  # [B, base_ch]
        t_emb = self.time_proj(t_emb)                    # [B, temb_dim]

        # Encoder path - start with downsampling
        h = self.conv_in(x)  # [B, base_ch, H, W]
        h = self.initial_downsample(h)  # [B, base_ch, H/2, W/2] - DOWNSAMPLE FIRST!
        
        encoder_features = []
        
        for i, (encoder, cross_blocks) in enumerate(zip(self.encoders, self.cross_encoders)):
            h = encoder(h, t_emb)
            
            # Apply cross attention blocks
            for cross_block in cross_blocks:
                h = cross_block(h, kv_features[i])
            
            encoder_features.append(h)
            
            # Downsample for next level (if not the last level)
            if i < len(self.downsamplers):
                h = self.downsamplers[i](h)

        # Decoder path
        for i, (upsampler, decoder, cross_blocks) in enumerate(zip(self.upsamplers, self.decoders, self.cross_decoders)):
            # Upsample
            h = upsampler(h)
            
            # Get corresponding encoder feature (in reverse order)
            skip_idx = len(encoder_features) - 2 - i  # -2 because we skip the deepest level
            skip_connection = encoder_features[skip_idx]
            
            # Concatenate with skip connection
            h = torch.cat([h, skip_connection], dim=1)
            
            # Decode
            h = decoder(h, t_emb)
            
            # Apply cross attention blocks
            kv_idx = skip_idx  # Use same index for kv_features
            for cross_block in cross_blocks:
                h = cross_block(h, kv_features[kv_idx])

        # Upsample back to original resolution
        h = self.final_upsample(h)  # [B, final_ch, H, W]
        
        # Final output
        out = self.final(h)
        return out.permute(0, 2, 3, 1)  # [B, H, W, out_ch]


# ---------------------------------------------------------
# 7) Top-level model: prompts encoder + multi-res UNet
# ---------------------------------------------------------

class TransUNet_small(nn.Module):
    """
    Full model with initial downsampling to avoid OOM:

      - PromptEncoderUNet encodes f_set into multi-scale KV features
        at resolutions H/2, H/4, H/8, ... (determined by mul_ls)
        (after permutation-invariant mean pooling over N)

      - MultiResUNetCrossAttention denoises x_t with time t,
        using multi-resolution cross-attention against those KV maps.
        Upsamples back to original H×W resolution at the end.
    """

    def __init__(
        self,
        in_ch: int = 1,
        out_ch: int = 1,
        base_ch: int = 64,
        groups: int = 4,
        dropout: float = 0.1,
        heads: int = 8,
        mul_ls: List[int] = [1, 2, 4],
        n_cross_per_level: int = 2,
    ):
        super().__init__()
        self.mul_ls = mul_ls

        self.prompt_encoder = PromptEncoderUNet(
            in_ch=in_ch,
            base_ch=base_ch,
            groups=groups,
            dropout=dropout,
            mul_ls=mul_ls,
            temb_dim=base_ch * 4,  # ← same temb_dim as the UNet
            heads=heads,           # ← self-attn heads for PromptSetTransformer
        )

        self.unet = MultiResUNetCrossAttention(
            in_ch=in_ch,
            out_ch=out_ch,
            base_ch=base_ch,
            groups=groups,
            dropout=dropout,
            heads=heads,
            mul_ls=mul_ls,
            n_cross_per_level=n_cross_per_level,
        )

    def forward(
        self,
        f_set: torch.Tensor,
        x_t: torch.Tensor,
        t: torch.Tensor,
    ) -> torch.Tensor:
        """
        f_set: [N, H, W, 1] or [N, 1, H, W]   (unordered set of prompts)
        x_t:   [B, H, W, 1] or [B, 1, H, W]
        t:     [B]
        """
        # 1) compute time embedding first (so prompt encoder can use it)
        t_emb_raw = get_timestep_embedding(t, self.unet.base_ch)      # [B, base_ch]
        t_emb = self.unet.time_proj(t_emb_raw)                        # [B, temb_dim]
        # pass raw sinusoidal emb (base_ch) to prompt encoder's own time_proj
        t_emb_prompt = t_emb_raw.mean(dim=0)                          # [base_ch]

        # 2) encode prompts → multi-scale KV, now time-aware + self-attn over N
        prompt_features = self.prompt_encoder(f_set, temb=t_emb_prompt)

        # permutation-invariant pooling over set dimension N
        kv_features = [h.mean(dim=0) for h in prompt_features]

        # 3) time-conditioned UNet with multi-res cross-attention
        eps = self.unet(x_t, t, kv_features)

        return eps
