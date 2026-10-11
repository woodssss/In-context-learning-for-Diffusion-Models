module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/- Local algebraic checks for generalization_error.tex.
   Analytic/probabilistic premises are explicit hypotheses, not axioms.
   This file does NOT claim a full formalization of the population theorem. -/
namespace GeneralizationCheck

theorem residual_cancel (a s g x e : ℝ) (hs : s ≠ 0) :
    -(a*x+s*e)/s^2 + a*g/s^2 + e/s = a/s^2*(g-x) := by
  field_simp
  ring

theorem coordinate_error_bound (g x R b : ℝ)
    (hg : -R ≤ g ∧ g ≤ R) (hx : -b ≤ x ∧ x ≤ b) :
    (g-x)^2 ≤ (R+b)^2 := by
  have h1 : 0 ≤ R+b-(g-x) := by linarith
  have h2 : 0 ≤ R+b+(g-x) := by linarith
  nlinarith [mul_nonneg h1 h2]

theorem vector_error_bound (D : ℕ) (g x : Fin D → ℝ) (R b : ℝ)
    (hg : ∀ i, -R ≤ g i ∧ g i ≤ R) (hx : ∀ i, -b ≤ x i ∧ x i ≤ b) :
    (∑ i, (g i-x i)^2) ≤ D*(R+b)^2 := by
  calc
    (∑ i, (g i-x i)^2) ≤ ∑ _i : Fin D, (R+b)^2 :=
      Finset.sum_le_sum (fun i _ => coordinate_error_bound (g i) (x i) R b (hg i) (hx i))
    _ = D*(R+b)^2 := by simp

theorem square_completion (y a x z : ℝ) :
    2*(y-a*x)^2-(y-a*z)^2 = (y-a*(2*x-z))^2-2*a^2*(x-z)^2 := by
  ring

theorem vector_square_completion {ι : Type*} (S : Finset ι)
    (y x z : ι → ℝ) (a : ℝ) :
    2*(∑ i ∈ S, (y i-a*x i)^2)-(∑ i ∈ S, (y i-a*z i)^2) =
    (∑ i ∈ S, (y i-a*(2*x i-z i))^2)-2*a^2*(∑ i ∈ S, (x i-z i)^2) := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem density_cancellation (c m v : ℝ) (hm : m ≠ 0) :
    (v/m^2)*(c*m) = c*(v/m) := by
  field_simp

theorem cell_mass_cancellation (p v m : ℝ) (hp : p ≠ 0) :
    (p*v)/(p*m) = v/m := by
  simp [mul_div_mul_left, hp]

theorem partition_ratio {ι : Type*} (S : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hb : ∀ i ∈ S, 0 < b i) :
    (∑ i ∈ S, a i)/(∑ i ∈ S, b i) ≤ ∑ i ∈ S, a i / b i := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  apply div_le_div_of_nonneg_left (ha i hi) (hb i hi)
  exact Finset.single_le_sum (fun j hj => le_of_lt (hb j hj)) hi

theorem good_event_division (u m : ℝ) (hu : 0 ≤ u) (hm : 0 < m)
    (v : ℝ) (hv : m/2 ≤ v) : u/v^2 ≤ 4*u/m^2 := by
  have hvp : 0 < v := by linarith
  rw [div_le_div_iff₀ (sq_pos_of_pos hvp) (sq_pos_of_pos hm)]
  have hsq : m^2 ≤ 4*v^2 := by nlinarith [sq_nonneg (v-m/2)]
  nlinarith [mul_nonneg hu (show 0 ≤ 4*v^2-m^2 by linarith)]

theorem fixed_query_combination (B n r good bad : ℝ)
    (hB : 0 ≤ B) (hn : 0 < n)
    (hg : good ≤ 4*B/n*r) (hb : bad ≤ 4*B/n*(r-1)) :
    good+bad ≤ 8*B/n*r := by
  have h : 0 ≤ 4*B/n := by positivity
  calc
    good+bad ≤ 4*B/n*r + 4*B/n*(r-1) := add_le_add hg hb
    _ = 8*B/n*r-4*B/n := by ring
    _ ≤ 8*B/n*r := sub_le_self _ h

theorem candidate_tail_transfer (err kernel B q factor : ℝ)
    (hf : 0 ≤ factor) (he : err ≤ kernel+B*q) :
    factor*err ≤ factor*kernel+factor*B*q := by
  nlinarith

theorem tail_remainder (s q B : ℝ) (hs : 0 < s) (hB : 0 ≤ B)
    (hq : q ≤ s^6) : B/s^4*q ≤ B*s^2 := by
  have h := mul_le_mul_of_nonneg_left hq (show 0 ≤ B/s^4 by positivity)
  have he : B/s^4*s^6 = B*s^2 := by field_simp
  simpa [he] using h

theorem erm_decomposition (popLearn empLearn popCand empCand oracle : ℝ)
    (herm : empLearn ≤ empCand) :
    popLearn-oracle ≤ (popLearn-empLearn)+(empCand-popCand)+(popCand-oracle) := by
  linarith

theorem combine_errors (risk statI statII approx statBound approxBound : ℝ)
    (hd : risk ≤ statI+statII+approx) (hI : statI ≤ statBound)
    (hII : statII = 0) (hA : approx ≤ approxBound) :
    risk ≤ statBound+approxBound := by linarith

theorem exponent_balance (d : ℝ) (hd : 0 ≤ d) :
    -1 + (d+4)/(d+6) = -2/(d+6) := by
  have h : d+6 ≠ 0 := by linarith
  field_simp
  ring

theorem exponent_weight (d : ℝ) (hd : 0 ≤ d) :
    2+8/(d+6) = (2*d+20)/(d+6) := by
  have h : d+6 ≠ 0 := by linarith
  field_simp
  ring

theorem cutoff_squared (n d : ℝ) (hn : 0 < n) :
    (n ^ (-1/(d+6)))^2 = n ^ (-2/(d+6)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hn)]
  congr 1
  ring

theorem cutoff_approximation (n d : ℝ) (hn : 0 < n) (hd : 0 ≤ d) :
    1 / (n * (n ^ (-1/(d+6))) ^ (d+4)) = n ^ (-2/(d+6)) := by
  rw [← Real.rpow_mul (le_of_lt hn)]
  conv_lhs => arg 2; arg 1; rw [← Real.rpow_one n]
  rw [← Real.rpow_add hn, one_div, ← Real.rpow_neg (le_of_lt hn)]
  congr 1
  have h : d+6 ≠ 0 := by linarith
  field_simp
  ring

theorem cutoff_weight (n d : ℝ) (hn : 0 < n) (hd : 0 ≤ d) :
    n^2 / (n ^ (-1/(d+6)))^8 = n ^ ((2*d+20)/(d+6)) := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_natCast _ 8,
    ← Real.rpow_mul (le_of_lt hn), ← Real.rpow_sub hn]
  congr 1
  have h : d+6 ≠ 0 := by linarith
  field_simp
  ring

theorem statistical_dimension_power (D : ℝ) (hD : 0 < D) :
    D * Real.sqrt (D^3) = D ^ (5/2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast D 3,
    ← Real.rpow_mul (le_of_lt hD)]
  conv_lhs => arg 1; rw [← Real.rpow_one D]
  rw [← Real.rpow_add hD]
  norm_num

theorem statistical_context_power (n d : ℝ) (hn : 0 < n) :
    Real.sqrt n / (n ^ (-1/(d+6)))^4 = n ^ (1/2+4/(d+6)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast _ 4,
    ← Real.rpow_mul (le_of_lt hn), ← Real.rpow_sub hn]
  congr 1
  ring

theorem log_exponent_bound (d : ℝ) (hd : 0 ≤ d) :
    1+1/(d+6) ≤ 2 := by
  have h : 0 < d+6 := by linarith
  have : 1/(d+6) ≤ 1 := (div_le_iff₀ h).2 (by linarith)
  linarith

theorem logarithm_simplification (n d A : ℝ) (hn : 1 ≤ n)
    (hd : 0 ≤ d) (hA : 0 < A) :
    Real.log (n ^ (1+1/(d+6)) * A) ≤ Real.log (n^2*A) := by
  have hnp : 0 < n := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hn (log_exponent_bound d hd)
  have hp' : n ^ (1+1/(d+6)) ≤ n^2 := by simpa using hp
  apply Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hnp _) hA)
  exact mul_le_mul_of_nonneg_right hp' (le_of_lt hA)

#print axioms residual_cancel
#print axioms coordinate_error_bound
#print axioms vector_error_bound
#print axioms square_completion
#print axioms vector_square_completion
#print axioms density_cancellation
#print axioms cell_mass_cancellation
#print axioms partition_ratio
#print axioms good_event_division
#print axioms fixed_query_combination
#print axioms candidate_tail_transfer
#print axioms tail_remainder
#print axioms erm_decomposition
#print axioms combine_errors
#print axioms exponent_balance
#print axioms exponent_weight
#print axioms cutoff_squared
#print axioms cutoff_approximation
#print axioms cutoff_weight
#print axioms statistical_dimension_power
#print axioms statistical_context_power
#print axioms log_exponent_bound
#print axioms logarithm_simplification
end GeneralizationCheck
