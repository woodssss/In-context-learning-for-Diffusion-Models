module

public import ICLGeneralization.RatioEstimator
public import ICLGeneralization.QueryDensity
public import ICLGeneralization.RealizationReadout

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

set_option maxHeartbeats 2000000

noncomputable def ambientCleanLaw {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S) :
    Measure (KernelSpace D) := Measure.map Subtype.val μ

instance {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (ambientCleanLaw μ) :=
  (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).2 inferInstance

theorem ambient_clean_support {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (hS : MeasurableSet S) : ∀ᵐ x ∂ambientCleanLaw μ, x ∈ S := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable hS).2
  exact Filter.Eventually.of_forall (fun x => x.property)

theorem ambient_clean_integral {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (f : KernelSpace D → ℝ) (hf : Measurable f) :
    (∫ x, f x ∂ambientCleanLaw μ) = ∫ x : S, f x.val ∂μ :=
  integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable

noncomputable def sampleWeight {D : ℕ} {S : Set (KernelSpace D)} (a s : ℝ)
    (y : KernelSpace D) (x : S) : ℝ := kernel (1/(2*s^2)) y (a • x.val)

theorem sample_weight_bounds {D : ℕ} {S : Set (KernelSpace D)} (a s : ℝ)
    (y : KernelSpace D) (x : S) : 0 < sampleWeight a s y x ∧ sampleWeight a s y x ≤ 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    have h : 0 ≤ 1/(2*s^2)*‖y-a • x.val‖^2 := by positivity
    simpa only [neg_mul] using neg_nonpos.mpr h

theorem measurable_sample_weight {D : ℕ} {S : Set (KernelSpace D)} (a s : ℝ) :
    Measurable (fun p : KernelSpace D × S => sampleWeight a s p.1 p.2) := by
  unfold sampleWeight kernel
  fun_prop

theorem measurable_fixed_sample_weight {D : ℕ} {S : Set (KernelSpace D)} (a s : ℝ) (y : KernelSpace D) :
    Measurable (sampleWeight a s y : S → ℝ) := by
  unfold sampleWeight kernel
  fun_prop

theorem measurable_clean_coordinate {D : ℕ} {S : Set (KernelSpace D)} (j : Fin D) :
    Measurable (fun x : S => x.val j) := (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) j).measurable.comp measurable_subtype_coe

noncomputable def kernelModelMean {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (y : KernelSpace D) (j : Fin D) : ℝ :=
  weightedMean μ (sampleWeight a s y) (fun x => x.val j)

noncomputable def kernelModelError (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) : ℝ :=
  ratioError n D μ (sampleWeight a s y) (fun j x => x.val j) ω

theorem measurable_kernel_model_mean {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    [IsFiniteMeasure μ] (a s : ℝ) (j : Fin D) : Measurable (fun y => kernelModelMean μ a s y j) := by
  have hnum : Measurable (fun p : KernelSpace D × S => sampleWeight a s p.1 p.2*p.2.val j) := by
    exact (measurable_sample_weight a s).mul (by fun_prop)
  exact hnum.stronglyMeasurable.integral_prod_right.measurable.div
    (measurable_sample_weight a s).stronglyMeasurable.integral_prod_right.measurable

theorem measurable_kernel_model_error (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    [IsFiniteMeasure μ] (a s : ℝ) :
    Measurable (fun p : KernelSpace D × (Fin n → S) => kernelModelError n D μ a s p.1 p.2) := by
  unfold kernelModelError ratioError
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun p : KernelSpace D × (Fin n → S) => kernelModelMean μ a s p.1 j) :=
    (measurable_kernel_model_mean μ a s j).comp measurable_fst
  have hnum : Measurable (fun p : KernelSpace D × (Fin n → S) =>
      sampleAverage n (fun x : S => sampleWeight a s p.1 x*x.val j) p.2) := by
    unfold sampleAverage
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    unfold sampleWeight kernel
    fun_prop
  have hden : Measurable (fun p : KernelSpace D × (Fin n → S) =>
      sampleAverage n (sampleWeight a s p.1) p.2) := by
    unfold sampleAverage
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i _
    unfold sampleWeight kernel
    fun_prop
  exact ((hnum.div hden).sub hm).pow_const 2

theorem kernel_model_mean_bounds {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    [IsProbabilityMeasure μ] (b : ℝ) (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (a s : ℝ) (y : KernelSpace D) (j : Fin D) : kernelModelMean μ a s y j ∈ Set.Icc (-b) b := by
  have hw : Measurable (sampleWeight a s y : S → ℝ) := measurable_fixed_sample_weight a s y
  have hwLp := bounded_real_memLp μ (sampleWeight a s y) hw 1
    (fun x => by rw [abs_of_pos (sample_weight_bounds a s y x).1]; exact (sample_weight_bounds a s y x).2) 2
  have hwxLp : MemLp (fun x : S => sampleWeight a s y x*x.val j) 2 μ := by
    apply bounded_real_memLp μ _ (hw.mul (measurable_clean_coordinate j)) b
    intro x
    change |sampleWeight a s y x*x.val j| ≤ b
    rw [abs_mul, abs_of_pos (sample_weight_bounds a s y x).1]
    exact (mul_le_mul (sample_weight_bounds a s y x).2 (abs_le.mpr (hbox x.val x.property j))
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  exact weighted_mean_bounds μ _ _ b (hwLp.integrable (by norm_num)) (hwxLp.integrable (by norm_num))
    (Filter.Eventually.of_forall (fun x => (sample_weight_bounds a s y x).1.le))
    (Filter.Eventually.of_forall (fun x => hbox x.val x.property j))
    (positive_population_weight μ _ (hwLp.integrable (by norm_num)) (fun x => (sample_weight_bounds a s y x).1))

theorem kernel_model_error_bounds (n D : ℕ) (hn : 0 < n) {S : Set (KernelSpace D)} (μ : Measure S)
    [IsProbabilityMeasure μ] (b : ℝ) (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) :
    0 ≤ kernelModelError n D μ a s y ω ∧ kernelModelError n D μ a s y ω ≤ 4*(D : ℝ)*b^2 := by
  refine ⟨?_, ?_⟩
  · unfold kernelModelError ratioError
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h := vector_error_bound D (fun j => empiricalWeightedMean n (sampleWeight a s y) (fun x => x.val j) ω)
    (kernelModelMean μ a s y) b b
    (fun j => empirical_weighted_mean_bounds n hn _ _ b (fun x => (sample_weight_bounds a s y x).1)
      (fun x => hbox x.val x.property j) ω)
    (kernel_model_mean_bounds μ b hbox a s y)
  have he : (D : ℝ)*(b+b)^2=4*(D : ℝ)*b^2 := by ring
  exact h.trans_eq he

theorem kernel_model_error_integrable (n D : ℕ) (hn : 0 < n) {S : Set (KernelSpace D)}
    (μ : Measure S) [IsProbabilityMeasure μ] (ν : Measure (KernelSpace D)) [IsFiniteMeasure ν]
    (b : ℝ) (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (a s : ℝ) :
    Integrable (fun p : KernelSpace D × (Fin n → S) => kernelModelError n D μ a s p.1 p.2)
      (ν.prod (promptLaw n μ)) := by
  apply (bounded_real_memLp _ _ (measurable_kernel_model_error n D μ a s) (4*(D : ℝ)*b^2) _ 1).integrable (le_refl _)
  intro p
  rw [abs_of_nonneg (kernel_model_error_bounds n D hn μ b hbox a s p.1 p.2).1]
  exact (kernel_model_error_bounds n D hn μ b hbox a s p.1 p.2).2

theorem subtype_kernel_population_identity {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (y : KernelSpace D) :
    (∫ x, sampleWeight a s y x ∂μ) = populationKernel D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) y ∧
    (∫ x, sampleWeight a s y x^2 ∂μ) = populationKernelSquared D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) y := by
  constructor
  · exact (ambient_clean_integral μ (fun x => kernel (1/(2*s^2)) y (a • x)) (by unfold kernel; fun_prop)).symm
  · exact (ambient_clean_integral μ (fun x => kernel (1/(2*s^2)) y (a • x)^2) (by unfold kernel; fun_prop)).symm

theorem gaussian_query_ratio_integrable (D J : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (c : Fin J → KernelSpace D) (a s : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ s/2) :
    Integrable (fun y => populationKernelSquared D μ (fun x => a • x) (1/(2*s^2)) y/
      (populationKernel D μ (fun x => a • x) (1/(2*s^2)) y)^2)
      (gaussianQueryLaw D μ (fun x => a • x) (1/(2*s^2))) := by
  unfold gaussianQueryLaw
  rw [integrable_withDensity_iff_integrable_smul'
    ((measurable_population_kernel D μ (fun x => a • x) (by fun_prop) _).div_const _ |>.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he (y : KernelSpace D) :
      (ENNReal.ofReal (populationKernel D μ (fun x => a • x) (1/(2*s^2)) y/gaussianNormalizer D (1/(2*s^2)))).toReal •
      (populationKernelSquared D μ (fun x => a • x) (1/(2*s^2)) y/
      (populationKernel D μ (fun x => a • x) (1/(2*s^2)) y)^2) =
      populationKernelRatio D μ (fun x => a • x) (1/(2*s^2)) y/gaussianNormalizer D (1/(2*s^2)) := by
    have hnn : 0 ≤ populationKernel D μ (fun x => a • x) (1/(2*s^2)) y/gaussianNormalizer D (1/(2*s^2)) :=
      div_nonneg (population_kernel_nonnegative _ _ _ _ _) (gaussian_normalizer_positive D _ (by positivity)).le
    rw [ENNReal.toReal_ofReal hnn, smul_eq_mul]
    have hp := compact_population_kernel_positive D μ S hS hsupport (fun x => a • x) (by fun_prop) (1/(2*s^2)) y
    unfold populationKernelRatio
    field_simp
  simp_rw [he]
  exact (localized_kernel_ratio_integral D J μ S hS hsupport c a s ha hs hcover).1.div_const _

theorem kernel_sampling_cover_bound (n D J : ℕ) (hn : 0 < n) (S : Set (KernelSpace D))
    (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ] (b : ℝ) (hb : 0 ≤ b)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (c : Fin J → KernelSpace D)
    (a s : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ s/2) :
    (∫ y, (∫ ω, kernelModelError n D μ a s y ω ∂promptLaw n μ)
      ∂gaussianQueryLaw D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2))) ≤
        32*Real.exp 1*(D : ℝ)*b^2/(n : ℝ)*(J : ℝ) := by
  let ν := gaussianQueryLaw D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2))
  let : IsProbabilityMeasure ν := gaussian_query_law_probability D _ _ (by fun_prop) _ (by positivity)
  have hpoint (y : KernelSpace D) := fixed_query_ratio_error_bound n D hn μ (sampleWeight a s y)
    (fun j x => x.val j) b hb (measurable_fixed_sample_weight a s y) (sample_weight_bounds a s y)
    (fun j => measurable_clean_coordinate j) (fun j x => hbox x.val x.property j)
  have hquery := query_density_denominator_cancellation D J (ambientCleanLaw μ) S hS
    (ambient_clean_support μ hS.measurableSet) c a s ha hs hcover
  have hiq := gaussian_query_ratio_integrable D J (ambientCleanLaw μ) S hS
    (ambient_clean_support μ hS.measurableSet) c a s ha hs hcover
  have herr := (kernel_model_error_integrable n D hn μ ν b hbox a s).integral_prod_left
  have hineq : (∫ y, (∫ ω, kernelModelError n D μ a s y ω ∂promptLaw n μ) ∂ν) ≤
      32*(D : ℝ)*b^2/(n : ℝ)*(∫ y, populationKernelSquared D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) y/
        (populationKernel D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) y)^2 ∂ν) := by
    rw [← integral_const_mul]
    apply integral_mono_ae herr (hiq.const_mul _)
    exact Filter.Eventually.of_forall (fun y => by
      have h := hpoint y
      rw [(subtype_kernel_population_identity μ a s y).1, (subtype_kernel_population_identity μ a s y).2] at h
      exact h)
  have h := hineq.trans (mul_le_mul_of_nonneg_left hquery (by positivity))
  convert h using 1
  ring

#print axioms ambient_clean_support
#print axioms ambient_clean_integral
#print axioms sample_weight_bounds
#print axioms measurable_sample_weight
#print axioms measurable_fixed_sample_weight
#print axioms measurable_clean_coordinate
#print axioms measurable_kernel_model_mean
#print axioms measurable_kernel_model_error
#print axioms kernel_model_mean_bounds
#print axioms kernel_model_error_bounds
#print axioms kernel_model_error_integrable
#print axioms subtype_kernel_population_identity
#print axioms gaussian_query_ratio_integrable
#print axioms kernel_sampling_cover_bound
end GeneralizationCheck
