module

public import ICLGeneralization.Sampling
public import ICLGeneralization.Core

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def weightedMean (μ : Measure Ω) (w x : Ω → ℝ) : ℝ :=
  (∫ z, w z * x z ∂μ) / (∫ z, w z ∂μ)

theorem weighted_mean_bounds (μ : Measure Ω) (w x : Ω → ℝ) (b : ℝ)
    (hw : Integrable w μ) (hwx : Integrable (fun z => w z*x z) μ)
    (hwpos : ∀ᵐ z ∂μ, 0 ≤ w z) (hx : ∀ᵐ z ∂μ, x z ∈ Set.Icc (-b) b)
    (hm : 0 < ∫ z, w z ∂μ) : weightedMean μ w x ∈ Set.Icc (-b) b := by
  have hlo : (-b)*(∫ z, w z ∂μ) ≤ ∫ z, w z*x z ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hw.const_mul _) hwx
    filter_upwards [hwpos, hx] with z hz hxz
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hxz.1)]
  have hhi : (∫ z, w z*x z ∂μ) ≤ b*(∫ z, w z ∂μ) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hwx (hw.const_mul _)
    filter_upwards [hwpos, hx] with z hz hxz
    nlinarith [mul_nonneg hz (sub_nonneg.mpr hxz.2)]
  constructor
  · exact (le_div_iff₀ hm).2 hlo
  · exact (div_le_iff₀ hm).2 hhi

theorem centered_kernel_integral_zero (μ : Measure Ω) (w x : Ω → ℝ)
    (hw : Integrable w μ) (hwx : Integrable (fun z => w z*x z) μ)
    (hm : (∫ z, w z ∂μ) ≠ 0) :
    ∫ z, w z*(x z-weightedMean μ w x) ∂μ = 0 := by
  simp_rw [mul_sub]
  rw [integral_sub hwx (hw.mul_const _), integral_mul_const]
  unfold weightedMean
  field_simp
  ring

theorem centered_kernel_second_moment_bound (μ : Measure Ω) (w x : Ω → ℝ) (b c : ℝ)
    (hx : ∀ᵐ z ∂μ, x z ∈ Set.Icc (-b) b) (hc : c ∈ Set.Icc (-b) b)
    (hw2 : Integrable (fun z => (w z)^2) μ)
    (hf2 : Integrable (fun z => (w z*(x z-c))^2) μ) :
    (∫ z, (w z*(x z-c))^2 ∂μ) ≤ 4*b^2*(∫ z, (w z)^2 ∂μ) := by
  rw [← integral_const_mul]
  apply integral_mono_ae hf2 (hw2.const_mul _)
  filter_upwards [hx] with z hz
  have h := coordinate_error_bound (x z) c b b hz hc
  have hs : (x z-c)^2 ≤ 4*b^2 := by nlinarith
  simpa only [mul_pow, mul_comm] using mul_le_mul_of_nonneg_left hs (sq_nonneg (w z))

theorem centered_kernel_sample_second_moment (n : ℕ) (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w x : Ω → ℝ) (b : ℝ)
    (hw : Integrable w μ) (hwx : Integrable (fun z => w z*x z) μ)
    (hm : 0 < ∫ z, w z ∂μ)
    (hwpos : ∀ᵐ z ∂μ, 0 ≤ w z) (hx : ∀ᵐ z ∂μ, x z ∈ Set.Icc (-b) b)
    (hwL2 : MemLp w 2 μ)
    (hfL2 : MemLp (fun z => w z*(x z-weightedMean μ w x)) 2 μ) :
    (∫ ω, (sampleAverage n (fun z => w z*(x z-weightedMean μ w x)) ω)^2
      ∂promptLaw n μ) ≤ 4*b^2/(n : ℝ)*(∫ z, (w z)^2 ∂μ) := by
  rw [centered_sample_average_second_moment n hn μ _ hfL2
    (centered_kernel_integral_zero μ w x hw hwx (ne_of_gt hm))]
  have h := centered_kernel_second_moment_bound μ w x b (weightedMean μ w x)
    hx (weighted_mean_bounds μ w x b hw hwx hwpos hx hm)
    hwL2.integrable_sq hfL2.integrable_sq
  have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ ≤ (4*b^2*(∫ z, (w z)^2 ∂μ))/(n : ℝ) := div_le_div_of_nonneg_right h hnp.le
    _ = _ := by ring

theorem vector_centered_kernel_sample_second_moment (n D : ℕ) (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (x : Fin D → Ω → ℝ) (b : ℝ)
    (hw : Integrable w μ) (hwx : ∀ j, Integrable (fun z => w z*x j z) μ)
    (hm : 0 < ∫ z, w z ∂μ) (hwpos : ∀ᵐ z ∂μ, 0 ≤ w z)
    (hx : ∀ j, ∀ᵐ z ∂μ, x j z ∈ Set.Icc (-b) b)
    (hwL2 : MemLp w 2 μ)
    (hfL2 : ∀ j, MemLp (fun z => w z*(x j z-weightedMean μ w (x j))) 2 μ) :
    (∫ ω, ∑ j, (sampleAverage n (fun z => w z*(x j z-weightedMean μ w (x j))) ω)^2
      ∂promptLaw n μ) ≤ 4*(D : ℝ)*b^2/(n : ℝ)*(∫ z, (w z)^2 ∂μ) := by
  rw [integral_finsetSum]
  · calc
      _ ≤ ∑ _j : Fin D, 4*b^2/(n : ℝ)*(∫ z, (w z)^2 ∂μ) := by
        apply Finset.sum_le_sum
        intro j _
        exact centered_kernel_sample_second_moment n hn μ w (x j) b hw (hwx j)
          hm hwpos (hx j) hwL2 (hfL2 j)
      _ = _ := by simp; ring
  · intro j _
    exact (sample_average_memLp n μ _ (hfL2 j)).integrable_sq

#print axioms weighted_mean_bounds
#print axioms centered_kernel_integral_zero
#print axioms centered_kernel_second_moment_bound
#print axioms centered_kernel_sample_second_moment
#print axioms vector_centered_kernel_sample_second_moment
end GeneralizationCheck
