module

public import ICLGeneralization.GaussianQueryTransport
public import ICLGeneralization.MeasurableNetwork
public import ICLGeneralization.LemmaOne

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem kernel_coordinate_score_identity (D : ℕ) (a s : ℝ) (y x : KernelSpace D) :
    kernel (1/(2*s^2)) y (a • x) =
      Real.exp (-(∑ j, (y j-a*x j)^2)/(2*s^2)) := by
  unfold kernel
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  ring

theorem empirical_kernel_equals_softmax (n D : ℕ) (hn : 0 < n) (S : Set (KernelSpace D))
    (a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) (j : Fin D) :
    empiricalWeightedMean n (sampleWeight a s y) (fun x => x.val j) ω =
      softmaxReadout n (fun i => -(∑ r, (y r-a*(ω i).val r)^2)/(2*s^2)) (fun i => (ω i).val j) := by
  unfold empiricalWeightedMean sampleAverage softmaxReadout sampleWeight
  simp_rw [kernel_coordinate_score_identity]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  have hden : (∑ i, Real.exp (-(∑ r, (y r-a*(ω i).val r)^2)/(2*s^2))) ≠ 0 :=
    ne_of_gt (softmax_denominator_positive n hn _)
  simp_rw [mul_comm (Real.exp _) _]
  field_simp

noncomputable def candidateMean (n D : ℕ) {S : Set (KernelSpace D)} (b R C s0 a s : ℝ)
    (y : KernelSpace D) (ω : Fin n → S) (j : Fin D) : ℝ :=
  (kernelTransformer n D j (realizationM D b R s0 C) b).eval a s
    (fun i r => (ω i).val r) (fun r => y r)

noncomputable def candidateMeanError (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (b R C s0 a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) : ℝ :=
  ∑ j, (candidateMean n D b R C s0 a s y ω j-kernelModelMean μ a s y j)^2

theorem measurable_candidate_mean_error (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    [IsProbabilityMeasure μ] (b R C s0 a s : ℝ) :
    Measurable (fun p : KernelSpace D × (Fin n → S) => candidateMeanError n D μ b R C s0 a s p.1 p.2) := by
  unfold candidateMeanError
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun p : KernelSpace D × (Fin n → S) => kernelModelMean μ a s p.1 j) :=
    (measurable_kernel_model_mean μ a s j).comp measurable_fst
  have hg : Measurable (fun p : KernelSpace D × (Fin n → S) => candidateMean n D b R C s0 a s p.1 p.2 j) := by
    apply measurable_transformer_eval
    · intro i r
      exact (measurable_clean_coordinate r).comp ((measurable_pi_apply i).comp measurable_snd)
    · intro r
      exact (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) r).measurable.comp measurable_fst
  exact (hg.sub hm).pow_const 2

theorem candidate_mean_error_bounds (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    [IsProbabilityMeasure μ] (b R C s0 a s : ℝ) (hb : 0 ≤ b)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (y : KernelSpace D) (ω : Fin n → S) :
    0 ≤ candidateMeanError n D μ b R C s0 a s y ω ∧
      candidateMeanError n D μ b R C s0 a s y ω ≤ 4*(D : ℝ)*b^2 := by
  refine ⟨Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  have h := vector_error_bound D (candidateMean n D b R C s0 a s y ω) (kernelModelMean μ a s y) b b
    (fun j => kernel_transformer_global_bound n D j _ b a s hb _ _)
    (kernel_model_mean_bounds μ b hbox a s y)
  have he : (D : ℝ)*(b+b)^2=4*(D : ℝ)*b^2 := by ring
  exact h.trans_eq he

theorem candidate_mean_exact_good_noise (n D : ℕ) (hn : 0 < n) {S : Set (KernelSpace D)}
    (b R C s0 a s : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (ω : Fin n → S) (z : S) (eps : KernelSpace D)
    (heps : ‖eps‖ ≤ C) (j : Fin D) :
    candidateMean n D b R C s0 a s (a • z.val+s • eps) ω j =
      empiricalWeightedMean n (sampleWeight a s (a • z.val+s • eps)) (fun x => x.val j) ω := by
  rw [empirical_kernel_equals_softmax n D hn S a s _ ω j]
  exact kernel_transformer_exact n D hn j b R C a s s0 hb ha hs0 hs
    (fun i => (ω i).val) z.val eps (fun i r => hbox (ω i).val (ω i).property r)
    (hbox z.val z.property) heps

theorem candidate_error_pointwise_transfer (n D : ℕ) (hn : 0 < n) {S : Set (KernelSpace D)}
    (μ : Measure S) [IsProbabilityMeasure μ] (b R C s0 a s : ℝ) (hb : 0 ≤ b)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (ω : Fin n → S) (z : S) (eps : KernelSpace D) :
    candidateMeanError n D μ b R C s0 a s (a • z.val+s • eps) ω ≤
      kernelModelError n D μ a s (a • z.val+s • eps) ω+
        (if C < ‖eps‖ then 4*(D : ℝ)*b^2 else 0) := by
  split_ifs with hbad
  · have hg := (candidate_mean_error_bounds n D μ b R C s0 a s hb hbox (a • z.val+s • eps) ω).2
    have hk := (kernel_model_error_bounds n D hn μ b hbox a s (a • z.val+s • eps) ω).1
    linarith
  · simp only [add_zero]
    unfold candidateMeanError kernelModelError ratioError
    simp_rw [candidate_mean_exact_good_noise n D hn b R C s0 a s hb ha hs0 hs hbox ω z eps (le_of_not_gt hbad)]
    rfl

theorem bounded_probability_product_integrable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X × Y → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ p, |f p| ≤ B) :
    Integrable f (μ.prod ν) := (bounded_real_memLp _ f hf B hB 1).integrable (le_refl _)

#print axioms kernel_coordinate_score_identity
#print axioms empirical_kernel_equals_softmax
#print axioms measurable_candidate_mean_error
#print axioms candidate_mean_error_bounds
#print axioms candidate_mean_exact_good_noise
#print axioms candidate_error_pointwise_transfer
#print axioms bounded_probability_product_integrable
end GeneralizationCheck
