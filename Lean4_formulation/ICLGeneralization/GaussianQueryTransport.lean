module

public import ICLGeneralization.GaussianTail
public import ICLGeneralization.KernelSamplingModel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem scaled_gaussian_kernel (D : ℕ) (a s : ℝ) (hs : 0 < s) (x eps : KernelSpace D) :
    kernel (1/(2*s^2)) (a • x+s • eps) (a • x) = kernel (1/2) eps 0 := by
  unfold kernel
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs, sub_zero]
  congr 1
  field_simp

theorem gaussian_normalizer_scale (D : ℕ) (s : ℝ) (hs : 0 < s) :
    gaussianNormalizer D (1/(2*s^2)) = s^D*gaussianNormalizer D (1/2) := by
  have he (eps : KernelSpace D) : kernel (1/(2*s^2)) (s • eps) 0 = kernel (1/2) eps 0 := by
    simpa only [zero_smul, zero_add] using scaled_gaussian_kernel D 0 s hs 0 eps
  have h := Measure.integral_comp_smul volume (fun y : KernelSpace D => kernel (1/(2*s^2)) y 0) s
  simp_rw [he] at h
  rw [gaussian_kernel_integral D (1/2) (by norm_num) 0,
    gaussian_kernel_integral D (1/(2*s^2)) (by positivity) 0] at h
  have hd : Module.finrank ℝ (KernelSpace D)=D := by simp [KernelSpace]
  rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hs D)), smul_eq_mul] at h
  have hsn : s^D ≠ 0 := ne_of_gt (pow_pos hs D)
  field_simp at h
  nlinarith

theorem noisy_query_single_integral (D : ℕ) (a s : ℝ) (hs : 0 < s) (x : KernelSpace D)
    (f : KernelSpace D → ℝ) :
    (∫ eps, f (a • x+s • eps) ∂gaussianNoiseLaw D) =
      (∫ y, f y*kernel (1/(2*s^2)) y (a • x))/gaussianNormalizer D (1/(2*s^2)) := by
  unfold gaussianNoiseLaw
  rw [gaussian_query_integral D (Measure.dirac 0) id continuous_id (1/2) (by norm_num)]
  simp_rw [population_kernel_dirac, ← scaled_gaussian_kernel D a s hs x]
  let g : KernelSpace D → ℝ := fun y => f y*kernel (1/(2*s^2)) y (a • x)
  have hscale := Measure.integral_comp_smul volume (fun y => g (a • x+y)) s
  have hd : Module.finrank ℝ (KernelSpace D)=D := by simp [KernelSpace]
  rw [hd, abs_of_pos (inv_pos.mpr (pow_pos hs D)), smul_eq_mul,
    integral_add_left_eq_self g (a • x)] at hscale
  change (∫ eps, g (a • x+s • eps))/gaussianNormalizer D (1/2) = _
  rw [hscale, gaussian_normalizer_scale D s hs]
  dsimp only [g]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem bounded_gaussian_query_product_integrable (D : ℕ) (μ : Measure (KernelSpace D))
    [IsProbabilityMeasure μ] (a β : ℝ) (hβ : 0 < β) (f : KernelSpace D → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    Integrable (fun p : KernelSpace D × KernelSpace D => f p.2*kernel β p.2 (a • p.1))
      (μ.prod volume) := by
  let F : KernelSpace D × KernelSpace D → ℝ := fun p => f p.2*kernel β p.2 (a • p.1)
  have hF : Measurable F := by unfold F kernel; fun_prop
  have hnorm (x y : KernelSpace D) : ‖F (x,y)‖ ≤ C*kernel β y (a • x) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < kernel β y (a • x) from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hC y) (Real.exp_pos _).le
  have hslice (x : KernelSpace D) : Integrable (fun y => F (x,y)) :=
    ((gaussian_kernel_integrable D β hβ (a • x)).const_mul C).mono'
      (hF.comp ((measurable_const : Measurable (fun _ : KernelSpace D => x)).prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hnorm x))
  have houterbound (x : KernelSpace D) : (∫ y, ‖F (x,y)‖) ≤ C*gaussianNormalizer D β := by
    have h := integral_mono_ae (hslice x).norm ((gaussian_kernel_integrable D β hβ (a • x)).const_mul C)
      (Filter.Eventually.of_forall (hnorm x))
    rwa [integral_const_mul, gaussian_kernel_integral D β hβ (a • x)] at h
  apply (integrable_prod_iff hF.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
  apply (bounded_real_memLp μ _ hF.stronglyMeasurable.norm.integral_prod_right'.measurable
    (C*gaussianNormalizer D β) _ 1).integrable (le_refl _)
  intro x
  rw [abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  exact houterbound x

theorem clean_noise_query_integral (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (a s : ℝ) (hs : 0 < s) (f : KernelSpace D → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    (∫ x, (∫ eps, f (a • x+s • eps) ∂gaussianNoiseLaw D) ∂μ) =
      ∫ y, f y ∂gaussianQueryLaw D μ (fun x => a • x) (1/(2*s^2)) := by
  simp_rw [noisy_query_single_integral D a s hs _ f]
  rw [integral_div, gaussian_query_integral D μ (fun x => a • x) (by fun_prop) _ (by positivity)]
  congr 1
  have hi := bounded_gaussian_query_product_integrable D μ a (1/(2*s^2)) (by positivity) f hf C hC
  rw [integral_integral_swap hi]
  congr 1
  funext y
  rw [integral_const_mul]
  rfl

theorem subtype_clean_noise_query_integral (D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (a s : ℝ) (hs : 0 < s) (f : KernelSpace D → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) :
    (∫ x : S, (∫ eps, f (a • x.val+s • eps) ∂gaussianNoiseLaw D) ∂μ) =
      ∫ y, f y ∂gaussianQueryLaw D (ambientCleanLaw μ) (fun x => a • x) (1/(2*s^2)) := by
  have hm : Measurable (fun p : KernelSpace D × KernelSpace D => f (a • p.1+s • p.2)) := by fun_prop
  have hi : Measurable (fun x : KernelSpace D => ∫ eps, f (a • x+s • eps) ∂gaussianNoiseLaw D) :=
    hm.stronglyMeasurable.integral_prod_right (ν := gaussianNoiseLaw D) |>.measurable
  have he := ambient_clean_integral μ (fun x : KernelSpace D => ∫ eps, f (a • x+s • eps) ∂gaussianNoiseLaw D) hi
  rw [← he]
  exact clean_noise_query_integral D (ambientCleanLaw μ) a s hs f hf C hC

#print axioms scaled_gaussian_kernel
#print axioms gaussian_normalizer_scale
#print axioms noisy_query_single_integral
#print axioms bounded_gaussian_query_product_integrable
#print axioms clean_noise_query_integral
#print axioms subtype_clean_noise_query_integral
end GeneralizationCheck
