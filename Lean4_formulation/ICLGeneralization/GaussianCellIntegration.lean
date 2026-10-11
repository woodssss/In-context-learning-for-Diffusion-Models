module

public import ICLGeneralization.CompactKernel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

abbrev KernelSpace (D : ℕ) := EuclideanSpace ℝ (Fin D)

noncomputable def gaussianNormalizer (D : ℕ) (β : ℝ) : ℝ :=
  (Real.pi/β)^((D : ℝ)/2)

theorem gaussian_normalizer_positive (D : ℕ) (β : ℝ) (hβ : 0 < β) :
    0 < gaussianNormalizer D β := Real.rpow_pos_of_pos (div_pos Real.pi_pos hβ) _

theorem gaussian_pair_integral (D : ℕ) (β : ℝ) (hβ : 0 < β) (x z : KernelSpace D) :
    (∫ y, kernel β y x^2/kernel β y z) =
      Real.exp (2*β*‖x-z‖^2)*gaussianNormalizer D β := by
  have h := gaussian_ratio_integral β hβ x z
  have hd : Module.finrank ℝ (KernelSpace D) = D := by simp [KernelSpace]
  rw [hd] at h
  exact (div_eq_iff (ne_of_gt (gaussian_normalizer_positive D β hβ))).1 h

theorem gaussian_pair_integrable (D : ℕ) (β : ℝ) (hβ : 0 < β) (x z : KernelSpace D) :
    Integrable (fun y => kernel β y x^2/kernel β y z) := by
  by_contra h
  have he := gaussian_pair_integral D β hβ x z
  rw [integral_undef h] at he
  have hp := mul_pos (Real.exp_pos (2*β*‖x-z‖^2)) (gaussian_normalizer_positive D β hβ)
  linarith

noncomputable def populationKernel (D : ℕ) (μ : Measure (KernelSpace D))
    (center : KernelSpace D → KernelSpace D) (β : ℝ) (y : KernelSpace D) : ℝ :=
  ∫ x, kernel β y (center x) ∂μ

noncomputable def populationKernelSquared (D : ℕ) (μ : Measure (KernelSpace D))
    (center : KernelSpace D → KernelSpace D) (β : ℝ) (y : KernelSpace D) : ℝ :=
  ∫ x, kernel β y (center x)^2 ∂μ

noncomputable def populationKernelRatio (D : ℕ) (μ : Measure (KernelSpace D))
    (center : KernelSpace D → KernelSpace D) (β : ℝ) (y : KernelSpace D) : ℝ :=
  populationKernelSquared D μ center β y / populationKernel D μ center β y

theorem measurable_population_kernel (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) :
    Measurable (populationKernel D μ center β) := by
  have h : Continuous (fun p : KernelSpace D × KernelSpace D => kernel β p.1 (center p.2)) := by
    unfold kernel
    fun_prop
  exact h.measurable.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_population_kernel_squared (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) :
    Measurable (populationKernelSquared D μ center β) := by
  have h : Continuous (fun p : KernelSpace D × KernelSpace D => kernel β p.1 (center p.2)^2) := by
    unfold kernel
    fun_prop
  exact h.measurable.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_population_kernel_ratio (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) :
    Measurable (populationKernelRatio D μ center β) :=
  (measurable_population_kernel_squared D μ center hc β).div
    (measurable_population_kernel D μ center hc β)

theorem compact_population_kernel_positive (D : ℕ) (μ : Measure (KernelSpace D))
    [IsProbabilityMeasure μ] (S : Set (KernelSpace D)) (hS : IsCompact S)
    (hsupport : ∀ᵐ x ∂μ, x ∈ S) (center : KernelSpace D → KernelSpace D)
    (hc : Continuous center) (β : ℝ) (y : KernelSpace D) :
    0 < populationKernel D μ center β y := by
  apply integral_exp_pos
  apply compact_supported_continuous_integrable μ S hS hsupport
  fun_prop

theorem compact_cell_jensen (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (y : KernelSpace D) :
    populationKernelRatio D μ center β y ≤
      ∫ p, kernel β y (center p.1)^2/kernel β y (center p.2) ∂μ.prod μ := by
  have hi : Integrable (fun x => kernel β y (center x)) μ :=
    compact_supported_continuous_integrable μ S hS hsupport _ (by unfold kernel; fun_prop)
  have hinv : Integrable (fun x => 1/kernel β y (center x)) μ :=
    compact_supported_continuous_integrable μ S hS hsupport _
      (continuous_const.div (by unfold kernel; fun_prop) (fun _ => ne_of_gt (Real.exp_pos _)))
  have hj := integral_reciprocal_jensen μ _ hi hinv
    (Filter.Eventually.of_forall (fun _ => Real.exp_pos _))
    (compact_population_kernel_positive D μ S hS hsupport center hc β y)
  have hn : 0 ≤ populationKernelSquared D μ center β y := integral_nonneg (fun _ => sq_nonneg _)
  have h := mul_le_mul_of_nonneg_left hj hn
  unfold populationKernelSquared at h
  rw [← integral_prod_mul] at h
  unfold populationKernelRatio populationKernelSquared populationKernel
  convert h using 1
  · ring
  · congr 1
    funext p
    ring

theorem gaussian_cell_integrated_bound (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (hβ : 0 < β)
    (hdiam : ∀ᵐ p ∂μ.prod μ, 2*β*‖center p.1-center p.2‖^2 ≤ 1) :
    Integrable (populationKernelRatio D μ center β) ∧
      (∫ y, populationKernelRatio D μ center β y) ≤ Real.exp 1*gaussianNormalizer D β := by
  let F : (KernelSpace D × KernelSpace D) × KernelSpace D → ℝ :=
    fun p => kernel β p.2 (center p.1.1)^2/kernel β p.2 (center p.1.2)
  have hF : Continuous F := by
    unfold F kernel
    exact (by fun_prop : Continuous (fun p : (KernelSpace D × KernelSpace D) × KernelSpace D =>
      Real.exp (-β*‖p.2-center p.1.1‖^2)^2)).div (by fun_prop) (fun p => Real.exp_ne_zero _)
  have hnorm (p : KernelSpace D × KernelSpace D) :
      (∫ y, ‖F (p,y)‖) = Real.exp (2*β*‖center p.1-center p.2‖^2)*gaussianNormalizer D β := by
    simp only [Real.norm_eq_abs]
    have hnn (y : KernelSpace D) : 0 ≤ F (p,y) := div_nonneg (sq_nonneg _) (Real.exp_pos _).le
    simp_rw [abs_of_nonneg (hnn _)]
    exact gaussian_pair_integral D β hβ (center p.1) (center p.2)
  have houter : Integrable (fun p => ∫ y, ‖F (p,y)‖) (μ.prod μ) := by
    apply Integrable.mono' (integrable_const (Real.exp 1*gaussianNormalizer D β))
      hF.measurable.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hdiam] with p hp
    rw [hnorm, Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (gaussian_normalizer_positive D β hβ))]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp)
      (gaussian_normalizer_positive D β hβ).le
  have hjoint : Integrable F ((μ.prod μ).prod volume) :=
    (integrable_prod_iff hF.measurable.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall (fun p => gaussian_pair_integrable D β hβ (center p.1) (center p.2)), houter⟩
  have hrhs : Integrable (fun y => ∫ p, F (p,y) ∂μ.prod μ) := hjoint.integral_prod_right
  have hpoint (y : KernelSpace D) : populationKernelRatio D μ center β y ≤
      ∫ p, F (p,y) ∂μ.prod μ := compact_cell_jensen D μ S hS hsupport center hc β y
  have hratio : Integrable (populationKernelRatio D μ center β) := by
    apply Integrable.mono' hrhs
      (measurable_population_kernel_ratio D μ center hc β).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      have hnn : 0 ≤ populationKernelRatio D μ center β y := by
        unfold populationKernelRatio populationKernelSquared populationKernel
        exact div_nonneg (integral_nonneg (fun _ => sq_nonneg _))
          (integral_nonneg (fun _ => (Real.exp_pos _).le))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hpoint y)
  refine ⟨hratio, ?_⟩
  calc
    _ ≤ ∫ y, ∫ p, F (p,y) ∂μ.prod μ := integral_mono_ae hratio hrhs (Filter.Eventually.of_forall hpoint)
    _ = ∫ p, (∫ y, F (p,y)) ∂μ.prod μ := (integral_integral_swap hjoint).symm
    _ ≤ ∫ _p, Real.exp 1*gaussianNormalizer D β ∂μ.prod μ := by
      apply integral_mono_ae hjoint.integral_prod_left (integrable_const _)
      filter_upwards [hdiam] with p hp
      rw [gaussian_pair_integral D β hβ (center p.1) (center p.2)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp)
        (gaussian_normalizer_positive D β hβ).le
    _ = _ := by simp

#print axioms gaussian_normalizer_positive
#print axioms gaussian_pair_integral
#print axioms gaussian_pair_integrable
#print axioms measurable_population_kernel
#print axioms measurable_population_kernel_squared
#print axioms measurable_population_kernel_ratio
#print axioms compact_population_kernel_positive
#print axioms compact_cell_jensen
#print axioms gaussian_cell_integrated_bound
end GeneralizationCheck
