module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory Real
namespace GeneralizationCheck

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem norm_square_completion (y x z : V) :
    2*‖y-x‖^2-‖y-z‖^2 = ‖y-((2 : ℝ) • x-z)‖^2-2*‖x-z‖^2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_ofNat]
  rw [real_inner_comm z x, real_inner_comm y x, real_inner_comm y z]
  ring

noncomputable def kernel (b : ℝ) (y x : V) : ℝ := exp (-b*‖y-x‖^2)

theorem kernel_ratio_factorization (b : ℝ) (y x z : V) :
    kernel b y x ^ 2 / kernel b y z =
    exp (2*b*‖x-z‖^2) * kernel b y ((2 : ℝ) • x-z) := by
  unfold kernel
  rw [← exp_nat_mul, ← exp_sub, ← exp_add]
  congr 1
  have h := norm_square_completion y x z
  have hm := congrArg (fun q : ℝ => b*q) h
  push_cast
  nlinarith [hm]

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem gaussian_ratio_integral (b : ℝ) (hb : 0 < b) (x z : V) :
    (∫ y : V, kernel b y x ^ 2 / kernel b y z) /
        (π/b) ^ (Module.finrank ℝ V / 2 : ℝ) = exp (2*b*‖x-z‖^2) := by
  simp_rw [kernel_ratio_factorization]
  rw [integral_const_mul]
  unfold kernel
  rw [integral_sub_right_eq_self (fun y : V => exp (-b*‖y‖^2)) ((2 : ℝ) • x-z)]
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  have h : (π/b) ^ (Module.finrank ℝ V / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _)
  exact mul_div_cancel_right₀ _ h

theorem gaussian_cell_bound (b : ℝ) (hb : 0 < b) (x z : V)
    (hdiam : 2*b*‖x-z‖^2 ≤ 1) :
    (∫ y : V, kernel b y x ^ 2 / kernel b y z) /
        (π/b) ^ (Module.finrank ℝ V / 2 : ℝ) ≤ exp 1 := by
  rw [gaussian_ratio_integral b hb x z]
  exact Real.exp_le_exp.mpr hdiam

#print axioms norm_square_completion
#print axioms kernel_ratio_factorization
#print axioms gaussian_ratio_integral
#print axioms gaussian_cell_bound
end GeneralizationCheck
