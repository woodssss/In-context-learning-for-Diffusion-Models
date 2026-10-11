module

public import ICLGeneralization.LemmaFiveBudget

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

noncomputable def approximationWeightBudget (n D : ℕ) (b R s0 : ℝ) : ℝ :=
  41943040*(D : ℝ)^8*(n : ℝ)^2*b^8*R^4/s0^8

/- The complete probability statement under the paper's explicit geometric
   covering condition. The candidate is the actual shared five-block network;
   the oracle is a log-density derivative; every sampling law is explicit. -/
theorem lemma_five_complete (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R A s0 a s : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hs1 : s ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∀ j, InScalarTransformerClass
      (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (approximationWeightBudget n D b R s0)) ∧
    (∫ z : S, (∫ eps, (∫ ω, ∑ j,
      (candidateScore n D b R (noiseRadius D s0) s0 a s (a • z.val+s • eps) ω j-
        trueGaussianScore μ a s (a • z.val+s • eps) j)^2
      ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  constructor
  · intro j
    have hm := lemma_five_candidate_membership n D hD j b R s0 hb hR
    exact ⟨network_budget_mono _ _ _ hm.1 (lemma_five_weight_budget_order n D hn hD b R s0 hb hR hs0 hs01), hm.2⟩
  · exact lemma_five_gaussian_score_approximation n D d hn S hS μ b R A s0 a s hb hA
      hs0 hs01 ha hs hs1 hbox hcover

#print axioms lemma_five_complete
end GeneralizationCheck
