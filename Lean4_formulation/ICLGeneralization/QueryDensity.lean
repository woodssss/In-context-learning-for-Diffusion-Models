module

public import ICLGeneralization.KernelLocalization
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem gaussian_kernel_integral (D : ℕ) (β : ℝ) (hβ : 0 < β) (x : KernelSpace D) :
    (∫ y, kernel β y x) = gaussianNormalizer D β := by
  have h := gaussian_pair_integral D β hβ x x
  have he (y : KernelSpace D) : kernel β y x^2/kernel β y x = kernel β y x := by
    rw [pow_two]
    exact mul_div_cancel_right₀ _ (show kernel β y x ≠ 0 from ne_of_gt (Real.exp_pos _))
  simp_rw [he] at h
  simpa using h

theorem gaussian_kernel_integrable (D : ℕ) (β : ℝ) (hβ : 0 < β) (x : KernelSpace D) :
    Integrable (fun y => kernel β y x) := by
  by_contra h
  have he := gaussian_kernel_integral D β hβ x
  rw [integral_undef h] at he
  linarith [gaussian_normalizer_positive D β hβ]

theorem population_kernel_integral (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (hβ : 0 < β) :
    Integrable (populationKernel D μ center β) ∧
      (∫ y, populationKernel D μ center β y) = gaussianNormalizer D β := by
  let F : KernelSpace D × KernelSpace D → ℝ := fun p => kernel β p.2 (center p.1)
  have hF : Continuous F := by unfold F kernel; fun_prop
  have hnorm (x : KernelSpace D) : (∫ y, ‖F (x,y)‖) = gaussianNormalizer D β := by
    simp only [Real.norm_eq_abs]
    have hnn (y : KernelSpace D) : 0 ≤ F (x,y) := (Real.exp_pos _).le
    simp_rw [abs_of_nonneg (hnn _)]
    exact gaussian_kernel_integral D β hβ (center x)
  have hjoint : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hF.measurable.aestronglyMeasurable).2
    refine ⟨Filter.Eventually.of_forall (fun x => gaussian_kernel_integrable D β hβ (center x)), ?_⟩
    simp_rw [hnorm]
    exact integrable_const _
  refine ⟨hjoint.integral_prod_right, ?_⟩
  calc
    _ = ∫ x, (∫ y, F (x,y)) ∂μ := (integral_integral_swap hjoint).symm
    _ = gaussianNormalizer D β := by
      dsimp only [F]
      simp only [gaussian_kernel_integral D β hβ, integral_const, probReal_univ, one_smul]

noncomputable def gaussianQueryLaw (D : ℕ) (μ : Measure (KernelSpace D))
    (center : KernelSpace D → KernelSpace D) (β : ℝ) : Measure (KernelSpace D) :=
  volume.withDensity (fun y => ENNReal.ofReal (populationKernel D μ center β y/gaussianNormalizer D β))

theorem population_kernel_nonnegative (D : ℕ) (μ : Measure (KernelSpace D))
    (center : KernelSpace D → KernelSpace D) (β : ℝ) (y : KernelSpace D) :
    0 ≤ populationKernel D μ center β y := integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem gaussian_query_law_probability (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianQueryLaw D μ center β) := by
  constructor
  unfold gaussianQueryLaw
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hi := (population_kernel_integral D μ center hc β hβ).1.div_const (gaussianNormalizer D β)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y => div_nonneg (population_kernel_nonnegative D μ center β y)
      (gaussian_normalizer_positive D β hβ).le)), integral_div,
    (population_kernel_integral D μ center hc β hβ).2,
    div_self (ne_of_gt (gaussian_normalizer_positive D β hβ)), ENNReal.ofReal_one]

theorem gaussian_query_integral (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (hβ : 0 < β)
    (f : KernelSpace D → ℝ) :
    (∫ y, f y ∂gaussianQueryLaw D μ center β) =
      (∫ y, f y*populationKernel D μ center β y)/gaussianNormalizer D β := by
  unfold gaussianQueryLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_population_kernel D μ center hc β).div_const _ |>.ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (population_kernel_nonnegative D μ center β _)
    (gaussian_normalizer_positive D β hβ).le), smul_eq_mul]
  rw [← integral_div]
  congr 1
  funext y
  ring

theorem query_density_denominator_cancellation (D J : ℕ) (μ : Measure (KernelSpace D))
    [IsProbabilityMeasure μ] (S : Set (KernelSpace D)) (hS : IsCompact S)
    (hsupport : ∀ᵐ x ∂μ, x ∈ S) (c : Fin J → KernelSpace D) (a s : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s) (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ s/2) :
    (∫ y, populationKernelSquared D μ (fun x => a • x) (1/(2*s^2)) y /
      (populationKernel D μ (fun x => a • x) (1/(2*s^2)) y)^2
      ∂gaussianQueryLaw D μ (fun x => a • x) (1/(2*s^2))) ≤ (J : ℝ)*Real.exp 1 := by
  have hβ : 0 < 1/(2*s^2) := by positivity
  rw [gaussian_query_integral D μ (fun x => a • x) (by fun_prop) _ hβ]
  have he (y : KernelSpace D) :
      populationKernelSquared D μ (fun x => a • x) (1/(2*s^2)) y /
          (populationKernel D μ (fun x => a • x) (1/(2*s^2)) y)^2 *
          populationKernel D μ (fun x => a • x) (1/(2*s^2)) y =
        populationKernelRatio D μ (fun x => a • x) (1/(2*s^2)) y := by
    have hp := compact_population_kernel_positive D μ S hS hsupport (fun x => a • x)
      (by fun_prop) (1/(2*s^2)) y
    unfold populationKernelRatio
    field_simp
  simp_rw [he]
  have h := (localized_kernel_ratio_integral D J μ S hS hsupport c a s ha hs hcover).2
  exact (div_le_iff₀ (gaussian_normalizer_positive D _ hβ)).2 h

#print axioms gaussian_kernel_integral
#print axioms gaussian_kernel_integrable
#print axioms population_kernel_integral
#print axioms population_kernel_nonnegative
#print axioms gaussian_query_law_probability
#print axioms gaussian_query_integral
#print axioms query_density_denominator_cancellation
end GeneralizationCheck
