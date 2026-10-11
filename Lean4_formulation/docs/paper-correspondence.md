# Paper-to-Lean correspondence

The reference manuscript is `main_arxiv_v1.tex`; its compared snapshot is identified by SHA256 in [manuscript-reference.json](../verification/manuscript-reference.json). Labels are more stable than equation numbers, which change when the exposition is edited. This package includes proof source and its precise model, but does not include the LaTeX draft or a PDF.

## Entry points

| Paper claim | Manuscript label | Type | Lean support | Status | Reading instruction |
|---|---|---|---|---|---|
| Exact Transformer realization | `lemma:transformer_kernel_regression` | theorem | [LemmaOne.lean](../ICLGeneralization/LemmaOne.lean), `lemma_one_transformer_realization` | Supported under its explicit domain | Read the query-region and global-bound conclusions separately |
| Statistical error I | `lemma:stat_error_I` | theorem | [StatisticalUniformTime.lean](../ICLGeneralization/StatisticalUniformTime.lean), `lemma_two_uniform_time_original`; [StatisticalFinal.lean](../ICLGeneralization/StatisticalFinal.lean), `lemma_two_uniform_time_rate` | Supported | Explicit envelope and fixed budget constant are retained |
| Statistical error II | `lemma:stat_error_II` | theorem | [StatisticalUniformTime.lean](../ICLGeneralization/StatisticalUniformTime.lean), `lemma_three_uniform_time_original` | Supported in explicit epsilon-dependent form | Interpret cutoff-dependent big-O notation through the explicit bound |
| Loss covering | `lem:cover` | theorem | [LemmaFourFixedSampling.lean](../ICLGeneralization/LemmaFourFixedSampling.lean), `lemma_four_fixed_uniform_time` | Supported for the stated fixed-template/equal-width class | Use the proved recurrence, not a former unverified closed formula |
| Finite-prompt score approximation | `lem:approx` | theorem | [LemmaFiveComplete.lean](../ICLGeneralization/LemmaFiveComplete.lean), `lemma_five_complete` | Supported given polynomial covers | Covers are an input; the probability calculation is proved |
| Population approximation | `prop:approximation_error` | theorem | [PropositionOneUniformTime.lean](../ICLGeneralization/PropositionOneUniformTime.lean), `proposition_one_uniform_time` | Supported | Uses the actual full-Gaussian DSM identity and uniform-time law |
| Main expected-risk rate | `thm:generalization_error` | theorem | [MainInequality.lean](../ICLGeneralization/MainInequality.lean), `main_generalization_error_inequality` | Supported given a measurable ERM | Read `learn`, `hl`, and `herm` as explicit inputs |
| Existence/measurable selection of an ERM | No certified existential conclusion | limitation | Inputs to `main_generalization_error_inequality` | Not constructed | Do not describe the main theorem as proving existence |

## Connected proof routes

The kernel realization is implemented by actual Q/K/V and six-layer FFN records, positional selection, softmax normalization, and clipping. [ScheduledMatrices.lean](../ICLGeneralization/ScheduledMatrices.lean) proves the time-schedule identities. [NativeParameterBridge.lean](../ICLGeneralization/NativeParameterBridge.lean) and [NativeCoverMembership.lean](../ICLGeneralization/NativeCoverMembership.lean) identify the same realization with the parameterized family used for covering.

The probability proof includes independence and centered variance, random-denominator control, the Gaussian mixture query density, denominator cancellation, measurable support partitions, cellwise integration and Tonelli, the Gaussian tail, and the derivative of the actual log-density score. The DSM bridge proves the vanishing cross term rather than assuming the risk identity.

For Lemma 2, the manuscript's Rademacher/Dudley exposition and the Lean proof are different routes to the same stated explicit bound. Lean uses a finite parameter grid, conditional independent bounded-sampling estimates, and finite-maximum exponential moments. It does not assume a Rademacher/Dudley estimate or a statistical-error conclusion.

For Lemma 3, the formal proof first derives zero signed expectation for a fixed candidate under the hierarchical sampling law, then obtains the epsilon-dependent inequality. The current main theorem applies that inequality with $\epsilon=s_0^6$ and retains all three error terms. Its assembly does not eliminate Statistical Error II using equality to zero. The independent zero-expectation assembly is also preserved in `MainTheorem.lean`.

## Constants and dimensions

For the scalar parameter count,

```math
P_T=w(D+1)+L_T\{3m_Tw^2+L_{\mathrm{FFN}}(w^2+w)\}.
```

The biases are included. Under $w=2D+6$, $L_T=5$, $L_{\mathrm{FFN}}=6$, and $m_T=n$, Lean proves $DP_T\le3136nD^3$.

The inequality assembly uses the definitions in [MainInequalityAlgebra.lean](../ICLGeneralization/MainInequalityAlgebra.lean):

```math
C_1=\big(\operatorname{statisticalRateConstant}(41943040,b,R)+\sqrt3\big)(R+b)^2,
\qquad
C_2=32e\,2^db^2A_{\mathcal M}+4b^2+7(R+b)^2.
```

`main_weight_budget_cutoff` in [MainTheorem.lean](../ICLGeneralization/MainTheorem.lean) proves the coefficient order $D^8n^{(2d+20)/(d+6)}b^8R^4$.

## Conventions required when comparing the manuscript

- Mean networks belong to $\mathcal G$; the resulting score networks belong to $\mathcal T$.
- The active-token count is $n+1$. A padded token convention is not needed for the current main result.
- $R^{\mathcal L}$ bounds the pointwise DSM loss, not the score over the entire ambient space.
- A prompt and clean query are drawn once per $(k,j)$ and reused for that episode's $N_T$ time/noise draws. Training records retain the DSM label.
- The formal hypothesis class accepts ordered prompt tuples. Treating a generic member as a function of an unordered empirical measure is a separate invariance question.
- The loss envelope $D(R+b)^2/s_0^4$ must stay explicit when the cutoff depends on $n$.

These conventions identify the mathematics checked by Lean. The repository is not a claim that every printed matrix, citation, sentence, or alternative notation in the draft has been mechanically verified.
