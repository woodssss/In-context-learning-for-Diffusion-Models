# Formal statement and scope

The definitive statement is `main_generalization_error_inequality` in [MainInequality.lean](../ICLGeneralization/MainInequality.lean). This document translates its premises and describes the certified model.

## Explicit premises

- $n\ge2$, $D\ge1$, $K,J,N_T\ge1$, $d$ is a nonnegative integer, and $0<\delta<1$.
- Tasks have a probability law on a measurable task space. Their clean distributions form a measurable Markov kernel.
- The common support $S\subset\mathbb R^D$ is compact and contained in $[-b,b]^D$, with $b\ge1$ and $R\ge b$.
- `HasPolynomialBallCovers S d A` is supplied, with $A\ge0$. This requires a finite radius-$r$ ball cover of cardinality at most $A r^{-d}$ for each $0<r\le1$. Its centers may be anywhere in the ambient space; the manuscript's stronger condition with centers on $S$ supplies this premise.
- The prescribed schedules are measurable and satisfy $0\le\alpha(t)\le1$ and $s_0\le\sigma(t)\le1$. The cutoff is attained: $\sigma(\delta)=s_0=n^{-1/(d+6)}$.
- The learner is a measurable function of the complete training sample, takes values in the admissible parameter set, and minimizes the actual empirical Gaussian DSM loss over that set. These properties are inputs to the main theorem.

## Network

The realization uses five Transformer blocks, at most $n$ heads per block, $n+1$ tokens, embedding and FFN width $2D+6$, and six affine FFN layers. The first four blocks use ReLU attention. The final block uses prompt-masked softmax; its final FFN clips the mean output coordinate. Stacking $D$ scalar networks gives the mean network $G_\theta$.

The diffusion schedules and the time-modulation templates are prescribed. For each Q/K/V map, only its base matrix is a free parameter:

```math
A_\theta(t)=A_\theta^{(0)}+\alpha(t)A^{(\alpha)}+\sigma(t)^{-1}A^{(\sigma)}.
```

The base matrices, embedding, decoder, and all FFN matrices and biases are covered by the coefficient grid. The fixed templates are not additional trainable coefficients. Auxiliary modules with three independently trainable schedule groups provide stability bounds for a larger family; they do not change the parameter count used in the main theorem.

The mean output is bounded by $R$ on the full sampled-input domain. The score is

```math
T_\theta(y,t)=-\frac{y}{\sigma(t)^2}+\frac{\alpha(t)}{\sigma(t)^2}G_\theta(y,t).
```

It is the mean and the DSM residual-square loss that are bounded. No global bound on the score over all of $\mathbb R^D$ is claimed. An explicit sufficient coefficient budget is $41943040D^8n^2b^8R^4/s_0^8$.

## Sampling and loss

1. Draw $K$ independent tasks.
2. For each task, draw $J$ conditionally independent episodes. Each episode consists of $n$ iid prompt samples and one independent clean query from that task.
3. For each episode, draw $N_T$ independent pairs of uniform time on $[\delta,1]$ and standard Gaussian noise, sharing that episode's prompt and clean query.

The training sample retains the variables required to evaluate the loss, including the clean query and noise. The network input itself consists only of the prompt, noisy query, and time. The test sample is independent of training.

The full Gaussian law is used in training and population risks. The event $`\|\varepsilon\|\le C_\delta`$ restricts the input region only for exact kernel realization and loss covering. Its complement is controlled using a proved Gaussian tail bound.

For $y=\alpha(t)x+\sigma(t)\varepsilon$, cancellation gives the pointwise loss bound

```math
\left\|T_\theta(y,t)+\frac{\varepsilon}{\sigma(t)}\right\|^2
=\frac{\alpha(t)^2}{\sigma(t)^4}\|G_\theta(y,t)-x\|^2
\le M_\delta:=\frac{D(R+b)^2}{s_0^4}.
```

The formal input is an ordered iid prompt tuple. A claim that every network in the hypothesis class factors through an unordered empirical measure requires a separate permutation-invariance argument and is not supplied here.

## Certified obligations

| Result | Assumptions | Dependencies | Obligation | Coverage | Risk or limit | Interpretation |
|---|---|---|---|---|---|---|
| Lemma 1 | Bounded prompts, legal schedules and query region | Explicit matrix selectors and clipping FFN | One shared candidate, exact kernel output, coefficient and output bounds | Covered | Exactness is restricted to the stated query region | Keep the region restriction |
| Lemma 4 | Fixed templates, equal widths, bounded coefficients and outputs | Softmax/network stability and internal parameter grid | Restricted loss covers and conditional-average covers | Covered | Arbitrary unequal widths are not the asserted specialization | Use the concrete architecture |
| Lemmas 2/3 | Independent hierarchy and bounded full loss | Conditional independent sampling and finite grids | Explicit expected statistical inequalities | Covered | Retain the cutoff-dependent envelope | Use the explicit inequalities |
| Lemma 5 / Proposition 1 | Compact bounded support and polynomial covers | Variance, Chebyshev, mixture density, partitions, Tonelli, Gaussian tails and DSM | Actual finite-prompt score and population-risk approximation | Covered | Geometry supplies the cover condition | Treat it as a premise |
| Main rate | All model premises and supplied measurable ERM | Certified statistics, approximation, candidate/risk bridges and cutoff algebra | Actual expected excess-risk bound | Covered | No claim of ERM existence | Conditional theorem |
| ERM construction | A selection theorem would require its own premises | Not implemented | Existence and measurable choice | Outside scope | Not a conclusion of this project | Supply the learner |
| Geometric derivation | Smooth-manifold hypotheses | Not implemented | Derive polynomial covers from geometry | Outside scope | Cover condition is an explicit input | Supply the cover condition |

## Limits of the certificate

The certificate concerns an expected score/DSM risk bound under this model. It does not prove an optimization guarantee for Adam, a sample-quality or reverse-SDE discretization bound, an out-of-distribution guarantee, or a theorem for the experimental U-Net and finite data-bank training procedure. It does not certify every statement in the manuscript or optimize the constants.

Mathlib supplies foundational analysis and probability results. Network realization, softmax stability, probability bridges, and the assembled bound are proved in this library; no bibliographic citation is substituted for a Lean proof of a paper-specific conclusion.
