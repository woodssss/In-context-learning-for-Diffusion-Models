# Lean proofs for in-context diffusion generalization

This repository contains a machine-checked Lean 4 formalization of the generalization analysis for in-context diffusion score matching, built on [mathlib](https://github.com/leanprover-community/mathlib4). It accompanies the theoretical results in `main_arxiv_v1.tex`.

## What is proved

The development establishes the following mathematical results:

- **Transformer realization:** an explicit five-block network exactly realizes the empirical Gaussian-kernel conditional mean on the stated query region, with a globally bounded mean output and a proved coefficient budget.
- **Finite-prompt approximation:** independent prompt sampling gives the score approximation bound, including random-denominator control, Gaussian query integration, measurable support partitions, and the noise-tail remainder.
- **Population DSM approximation:** a proved denoising score-matching identity transfers the score approximation to the population-loss difference.
- **Covering and statistical bounds:** the fixed-template network class has finite restricted-loss covers, yielding explicit statistical inequalities for the task, episode, and diffusion-sample levels.
- **Main generalization theorem:** these results combine into an expected excess-risk bound for a supplied measurable empirical risk minimizer.

The main theorem is stated and proved in [MainInequality.lean](ICLGeneralization/MainInequality.lean) as `GeneralizationCheck.main_generalization_error_inequality`. With the attained cutoff $s_0=\sigma(\delta)=n^{-1/(d+6)}$, its conclusion is

$$
\mathbb E_{\mathfrak S}\big[\mathcal L_n(T_{\theta^*;\mathfrak S})-\mathcal L(T^*)\big]
\le C_1D^{5/2}n^{1/2+4/(d+6)}\sqrt{\log(n^2DKJN_T)}
\left(\frac1{\sqrt K}+\frac1{\sqrt{KJ}}+\frac1{\sqrt{KJN_T}}\right)
+C_2D n^{-2/(d+6)}.
$$

Here $n$ is the context size, $D$ the ambient dimension, $d$ the covering exponent, $K$ the number of tasks, $J$ the episodes per task, and $N_T$ the diffusion samples per episode. The constant $C_1$ depends on $b,R$ and the fixed architecture and budget constants; $C_2$ depends on $b,R,d,A_{\mathcal M}$. Both are independent of the sample sizes, ambient dimension, and cutoff.

The results use the prescribed diffusion schedules, fixed time-modulation templates, and the independent hierarchical sampling law. The polynomial support-covering condition and a measurable admissible empirical minimizer are explicit premises. The network uses $n+1$ tokens, width $2D+6$, and six affine FFN layers. The complete assumptions and certification scope are in [proof-scope.md](docs/proof-scope.md).

## Guarantees

- **Complete Lean proofs.** The proof library contains no `sorry` or `admit`.
- **No custom axioms.** Every theorem's dependencies are printed with `#print axioms` and audited. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; `sorryAx` and unexpected axioms fail the check.
- **Reproducible verification.** [check.sh](check.sh) builds the library, checks every source file, and rejects compiler errors or warnings. The local checkpoint and source fingerprints are recorded in [verification.md](docs/verification.md).
- **Pinned dependencies.** [lean-toolchain](lean-toolchain) fixes Lean 4.35.0-rc4, a release candidate. Mathlib is fixed at `49fd9dee36e7bbf345fe7981d2de6aeeb591f75b`; [lake-manifest.json](lake-manifest.json) records the transitive revisions.

Verification uses Lean's typechecker and the theorem-dependency audit. A separate independent-kernel or comparator audit has not been performed. The [GitHub workflow](.github/workflows/check.yml) is configured to run the same checks; hosted CI has not yet been run for this package.

## Building

Install [elan](https://github.com/leanprover/elan), and have Git, Bash, and Python 3 available. From the directory containing `lean-toolchain`, run:

```sh
lake exe cache get
bash check.sh
```

The second command runs `lake build` and the full proof audit. Successful verification prints `PASS` and writes a fresh report to `.verification/report.json`. Keep the pinned compiler and dependency configuration when reproducing the checkpoint. Detailed instructions are in [reproduction.md](docs/reproduction.md).

After building, `import ICLGeneralization` loads the library, and `import ICLGeneralization.MainInequality` loads the main inequality declarations and their dependencies.

## Correspondence

| Manuscript result | Lean entry point | Source |
|---|---|---|
| Lemma 1: Transformer realization | `lemma_one_transformer_realization` | [LemmaOne.lean](ICLGeneralization/LemmaOne.lean) |
| Lemma 2: statistical error I | `lemma_two_uniform_time_original`, `lemma_two_uniform_time_rate` | [StatisticalUniformTime.lean](ICLGeneralization/StatisticalUniformTime.lean), [StatisticalFinal.lean](ICLGeneralization/StatisticalFinal.lean) |
| Lemma 3: statistical error II | `lemma_three_uniform_time_original` | [StatisticalUniformTime.lean](ICLGeneralization/StatisticalUniformTime.lean) |
| Lemma 4: restricted loss covering | `lemma_four_fixed_uniform_time` | [LemmaFourFixedSampling.lean](ICLGeneralization/LemmaFourFixedSampling.lean) |
| Lemma 5: finite-prompt probability bound | `lemma_five_complete` | [LemmaFiveComplete.lean](ICLGeneralization/LemmaFiveComplete.lean) |
| Proposition 1: population DSM approximation | `proposition_one_uniform_time` | [PropositionOneUniformTime.lean](ICLGeneralization/PropositionOneUniformTime.lean) |
| Main theorem: expected generalization rate | `main_generalization_error_inequality` | [MainInequality.lean](ICLGeneralization/MainInequality.lean) |

All declarations are in the `GeneralizationCheck` namespace. [paper-correspondence.md](docs/paper-correspondence.md) explains the proof routes and the relationship to the manuscript. In particular, the main assembly retains Statistical Error II through its inequality, and the statistical formalization uses a finite-grid proof of the stated bounds. The certified objects and premises are given by the linked Lean statements.

## Repository layout

```text
ICLGeneralization.lean          Library entry point
ICLGeneralization/             Proofs and supporting definitions
lean-toolchain                 Pinned Lean compiler
lakefile.toml                  Library and pinned mathlib dependency
lake-manifest.json             Transitive dependency revisions
check.sh                       Reproducible build and theorem audit
scripts/                       Audit and source-manifest tools
docs/                          Scope, correspondence, verification, publishing
verification/                  Publication checkpoint and file hashes
.github/workflows/check.yml    GitHub Actions proof audit
```

The source package is approximately 0.65 MB; dependencies and generated build files are fetched or created locally. For publication as a standalone repository or a subfolder, see [publishing.md](docs/publishing.md). See [CONTRIBUTING.md](CONTRIBUTING.md) for updating the proofs and checkpoint.

## License

The original proof code, audit tools, and documentation are released under the [MIT License](LICENSE). Dependencies retain their respective licenses.
