module

public import ICLGeneralization.NetworkRisk

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

/- The explicit geometric covering input is equation eq:cover-geometry in the
   paper. It is separate from the probability bound proved in this module. -/
def HasPolynomialBallCovers {D : ℕ} (S : Set (KernelSpace D)) (d : ℕ) (A : ℝ) : Prop :=
  ∀ (r : ℝ), 0 < r → r ≤ 1 → ∃ (J : ℕ) (c : Fin J → KernelSpace D),
    (J : ℝ) ≤ A/r^d ∧ ∀ x ∈ S, ∃ j, dist x (c j) ≤ r

noncomputable def approximationConstant (b : ℝ) (d : ℕ) : ℝ := 32*Real.exp 1*(2 : ℝ)^d*b^2

theorem approximation_schedule_scaling (n d : ℕ) (hn : 0 < n) (K B q a s s0 : ℝ)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hq : 0 ≤ q ∧ q ≤ s0^6)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    a^2/s^4*(K/((n : ℝ)*s^d)+B*q) ≤ K/((n : ℝ)*s0^(d+4))+B*s0^2 := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  have ha2 : a^2 ≤ 1 := by nlinarith
  have hf : a^2/s^4 ≤ 1/s0^4 := by
    calc
      _ ≤ 1/s^4 := div_le_div_of_nonneg_right ha2 (by positivity)
      _ ≤ 1/s0^4 := div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ hs0.le hs 4)
  have hfirst : a^2/s^4*(K/((n : ℝ)*s^d)) ≤ K/((n : ℝ)*s0^(d+4)) := by
    calc
      _ ≤ 1/s^4*(K/((n : ℝ)*s^d)) := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right ha2 (by positivity)) (by positivity)
      _ = K/((n : ℝ)*s^(d+4)) := by rw [pow_add]; ring
      _ ≤ _ := div_le_div_of_nonneg_left hK (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs0.le hs (d+4)) hnpos.le)
  have hsecond : a^2/s^4*(B*q) ≤ B*s0^2 := by
    calc
      _ ≤ 1/s0^4*(B*q) := mul_le_mul_of_nonneg_right hf (mul_nonneg hB hq.1)
      _ = B/s0^4*q := by ring
      _ ≤ _ := tail_remainder s0 q B hs0 hB hq.2
  rw [mul_add]
  exact add_le_add hfirst hsecond

theorem lemma_five_finite_prompt_approximation (n D d : ℕ) (hn : 0 < n)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R A s0 a s : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hs1 : s ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∫ z : S, (∫ eps, (∫ ω,
      scoreApproximationError n D μ b R (noiseRadius D s0) s0 a s (a • z.val+s • eps) ω
      ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  obtain ⟨J,c,hJ,hc⟩ := hcover (s/2) (by positivity) (by linarith)
  have hm := network_mean_approximation_cover_bound n D J hn S hS μ b R (noiseRadius D s0)
    s0 a s (by linarith) ha hs0 hs hbox c hc
  have htail := gaussian_tail_at_noise_radius D s0 hs0 hs01
  have htail0 : 0 ≤ (gaussianNoiseLaw D {eps | noiseRadius D s0 < ‖eps‖}).toReal := ENNReal.toReal_nonneg
  have hcov := mul_le_mul_of_nonneg_left hJ
    (show 0 ≤ 32*Real.exp 1*(D : ℝ)*b^2/(n : ℝ) by positivity)
  have hcov' : 32*Real.exp 1*(D : ℝ)*b^2/(n : ℝ)*(J : ℝ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s^d) := by
    unfold approximationConstant
    have he : 32*Real.exp 1*(D : ℝ)*b^2/(n : ℝ)*(A/(s/2)^d) =
        32*Real.exp 1*(2 : ℝ)^d*b^2*A*(D : ℝ)/((n : ℝ)*s^d) := by
      rw [div_pow]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
      field_simp
    exact hcov.trans_eq he
  have hm' := hm.trans (add_le_add hcov' (le_refl _))
  simp_rw [score_approximation_scaling]
  simp_rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left hm' (show 0 ≤ a^2/s^4 by positivity)
  exact h.trans (approximation_schedule_scaling n d hn (approximationConstant b d*A*(D : ℝ))
    (4*(D : ℝ)*b^2) _ a s s0 (by unfold approximationConstant; positivity) (by positivity)
    ⟨htail0,htail⟩ ha hs0 hs)

theorem lemma_five_candidate_membership (n D : ℕ) (hD : 1 ≤ D) (j : Fin D)
    (b R s0 : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) :
    InScalarTransformerClass (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (lemmaOneBudget n D (realizationM D b R s0 (noiseRadius D s0))) :=
  kernel_transformer_in_scalar_class n D hD j b R s0 (noiseRadius D s0) hb hR

#print axioms approximation_schedule_scaling
#print axioms lemma_five_finite_prompt_approximation
#print axioms lemma_five_candidate_membership
end GeneralizationCheck
