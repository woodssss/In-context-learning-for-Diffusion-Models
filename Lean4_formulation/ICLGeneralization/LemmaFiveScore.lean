module

public import ICLGeneralization.GaussianPosteriorScore

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem support_query_density_eq_gaussian_mixture (D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) (a s : ℝ) (y : KernelSpace D) :
    supportQueryDensity μ a s y =
      populationKernel D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) y/
        gaussianNormalizer D (1/(2*s^2)) := by
  unfold supportQueryDensity
  rw [(subtype_kernel_population_identity μ a s y).1]

/- Final Lemma 5 statement: the oracle in the squared error is the derivative
   of the actual log noisy-query density, rather than an assumed score formula.
   The iterated integrals use independent clean query, standard Gaussian noise,
   and the i.i.d. product-law prompt. -/
theorem lemma_five_gaussian_score_approximation (n D d : ℕ) (hn : 0 < n)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R A s0 a s : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hs1 : s ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∫ z : S, (∫ eps, (∫ ω, ∑ j,
      (candidateScore n D b R (noiseRadius D s0) s0 a s (a • z.val+s • eps) ω j-
        trueGaussianScore μ a s (a • z.val+s • eps) j)^2
      ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  simp_rw [true_gaussian_score_eq_posterior D S μ b a s (by linarith) ha
    (lt_of_lt_of_le hs0 hs) hbox]
  exact lemma_five_finite_prompt_approximation n D d hn S hS μ b R A s0 a s hb hA
    hs0 hs01 ha hs hs1 hbox hcover

theorem lemma_five_realized_candidate_and_error (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R A s0 a s : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hs1 : s ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∀ j, InScalarTransformerClass
      (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (lemmaOneBudget n D (realizationM D b R s0 (noiseRadius D s0)))) ∧
    (∫ z : S, (∫ eps, (∫ ω, ∑ j,
      (candidateScore n D b R (noiseRadius D s0) s0 a s (a • z.val+s • eps) ω j-
        trueGaussianScore μ a s (a • z.val+s • eps) j)^2
      ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 :=
  ⟨fun j => lemma_five_candidate_membership n D hD j b R s0 hb hR,
    lemma_five_gaussian_score_approximation n D d hn S hS μ b R A s0 a s hb hA
      hs0 hs01 ha hs hs1 hbox hcover⟩

#print axioms support_query_density_eq_gaussian_mixture
#print axioms lemma_five_gaussian_score_approximation
#print axioms lemma_five_realized_candidate_and_error
end GeneralizationCheck
