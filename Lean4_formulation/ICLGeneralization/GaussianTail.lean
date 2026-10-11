module

public import ICLGeneralization.QueryDensity

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

noncomputable def gaussianNoiseLaw (D : ℕ) : Measure (KernelSpace D) :=
  gaussianQueryLaw D (Measure.dirac 0) id (1/2)

instance (D : ℕ) : IsProbabilityMeasure (gaussianNoiseLaw D) :=
  gaussian_query_law_probability D (Measure.dirac 0) id continuous_id (1/2) (by norm_num)

theorem population_kernel_dirac (D : ℕ) (β : ℝ) (y : KernelSpace D) :
    populationKernel D (Measure.dirac 0) id β y = kernel β y 0 := by
  simp [populationKernel]

theorem gaussian_noise_exponential_moment (D : ℕ) :
    (∫ eps, Real.exp (‖eps‖^2/4) ∂gaussianNoiseLaw D) = (2 : ℝ)^((D : ℝ)/2) := by
  unfold gaussianNoiseLaw
  rw [gaussian_query_integral D (Measure.dirac 0) id continuous_id (1/2) (by norm_num)]
  simp_rw [population_kernel_dirac]
  have he (eps : KernelSpace D) : Real.exp (‖eps‖^2/4)*kernel (1/2) eps 0 = kernel (1/4) eps 0 := by
    unfold kernel
    rw [sub_zero, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [gaussian_kernel_integral D (1/4) (by norm_num) 0]
  unfold gaussianNormalizer
  rw [← Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp
  norm_num

theorem gaussian_noise_exponential_integrable (D : ℕ) :
    Integrable (fun eps => Real.exp (‖eps‖^2/4)) (gaussianNoiseLaw D) := by
  by_contra h
  have he := gaussian_noise_exponential_moment D
  rw [integral_undef h] at he
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ((D : ℝ)/2)
  linarith

theorem gaussian_norm_tail (D : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (gaussianNoiseLaw D {eps | C < ‖eps‖}).toReal ≤
      (2 : ℝ)^((D : ℝ)/2)/Real.exp (C^2/4) := by
  have hs : {eps : KernelSpace D | C < ‖eps‖} ⊆
      {eps | Real.exp (C^2/4) ≤ Real.exp (‖eps‖^2/4)} := by
    intro eps heps
    change C < ‖eps‖ at heps
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg eps]
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun eps : KernelSpace D => (Real.exp_pos (‖eps‖^2/4)).le))
    (gaussian_noise_exponential_integrable D) (Real.exp (C^2/4))
  rw [gaussian_noise_exponential_moment D] at hm
  exact (measureReal_mono hs).trans ((le_div_iff₀ (Real.exp_pos _)).2 (by simpa only [mul_comm] using hm))

noncomputable def noiseRadius (D : ℕ) (s0 : ℝ) : ℝ :=
  Real.sqrt (2*(D : ℝ)*Real.log 2+24*Real.log (1/s0))

theorem noise_radius_nonnegative (D : ℕ) (s0 : ℝ) : 0 ≤ noiseRadius D s0 := Real.sqrt_nonneg _

theorem noise_radius_squared (D : ℕ) (s0 : ℝ) (hs0 : 0 < s0) (hs1 : s0 ≤ 1) :
    (noiseRadius D s0)^2 = 2*(D : ℝ)*Real.log 2+24*Real.log (1/s0) := by
  apply Real.sq_sqrt
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hi : 1 ≤ 1/s0 := (le_div_iff₀ hs0).2 (by linarith)
  have hl : 0 ≤ Real.log (1/s0) := Real.log_nonneg hi
  positivity

theorem gaussian_tail_at_noise_radius (D : ℕ) (s0 : ℝ) (hs0 : 0 < s0) (hs1 : s0 ≤ 1) :
    (gaussianNoiseLaw D {eps | noiseRadius D s0 < ‖eps‖}).toReal ≤ s0^6 := by
  have ht := gaussian_norm_tail D (noiseRadius D s0) (noise_radius_nonnegative D s0)
  have he : (2 : ℝ)^((D : ℝ)/2)/Real.exp ((noiseRadius D s0)^2/4) = s0^6 := by
    rw [noise_radius_squared D s0 hs0 hs1, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_sub, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hs0), Real.log_one]
    have hex : Real.log 2*((D : ℝ)/2)-(2*(D : ℝ)*Real.log 2+24*(0-Real.log s0))/4 =
        6*Real.log s0 := by ring
    rw [hex]
    change Real.exp ((6 : ℕ)*Real.log s0) = s0^6
    rw [Real.exp_nat_mul, Real.exp_log hs0]
  exact ht.trans_eq he

#print axioms population_kernel_dirac
#print axioms gaussian_noise_exponential_moment
#print axioms gaussian_noise_exponential_integrable
#print axioms gaussian_norm_tail
#print axioms noise_radius_nonnegative
#print axioms noise_radius_squared
#print axioms gaussian_tail_at_noise_radius
end GeneralizationCheck
