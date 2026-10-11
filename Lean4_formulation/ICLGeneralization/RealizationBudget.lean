module

public import ICLGeneralization.RealizationRegion

@[expose] public section

namespace GeneralizationCheck

theorem realization_M_at_least_one (D : ℕ) (b R s0 C : ℝ) :
    1 ≤ realizationM D b R s0 C :=
  le_trans (le_max_left 1 R) (le_max_left _ _)

theorem realization_M_at_least_support (D : ℕ) (b R s0 C : ℝ) (hR : b ≤ R) :
    b ≤ realizationM D b R s0 C :=
  le_trans hR (le_trans (le_max_right 1 R) (le_max_left _ _))

theorem realization_M_reciprocal_control (D : ℕ) (hD : 1 ≤ D) (b R s0 C : ℝ)
    (hb : 1 ≤ b) (hs0 : 0 < s0) (hC : 0 ≤ C) :
    2/s0^2 ≤ realizationM D b R s0 C := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hroot : 1 ≤ Real.sqrt (D : ℝ) := by
    simpa using Real.sqrt_le_sqrt hDr
  have hprod : 2 ≤ 2*b*Real.sqrt (D : ℝ) := by
    nlinarith [mul_nonneg (show 0 ≤ b-1 by linarith) (show 0 ≤ Real.sqrt (D : ℝ)-1 by linarith)]
  have ht : 2/s0 ≤ 2*b*Real.sqrt (D : ℝ)/s0+C := by
    have h := div_le_div_of_nonneg_right hprod hs0.le
    linarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ 2/s0 by positivity) ht 2
  have he : (2/s0)^2/2 = 2/s0^2 := by field_simp
  have h := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)
  rw [he] at h
  exact h.trans (le_max_right _ _)

theorem schedule_matrix_factor_bound (M s s0 : ℝ) (hM : 1 ≤ M)
    (hrecip : 2/s0^2 ≤ M) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    1/(Real.sqrt 2*s) ≤ M := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  apply (sq_le_sq₀ (by positivity) (by linarith : 0 ≤ M)).1
  have he : (1/(Real.sqrt 2*s))^2 = 1/(2*s^2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [he]
  have hden : 2*s0^2 ≤ 2*s^2 := by nlinarith
  calc
    _ ≤ 1/(2*s0^2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ ≤ 2/s0^2 := by
      have he' : 1/(2*s0^2) = (1/2)/s0^2 := by ring
      rw [he']
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ M := hrecip
    _ ≤ M^2 := by nlinarith

theorem selector_coefficient_budget (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (M : ℝ) (hM : 1 ≤ M) :
    2*(4*M*(ℓ : ℝ)^2)+2 ≤ 10*(ℓ : ℝ)^2*M := by
  have hℓr : 1 ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hsq : 1 ≤ (ℓ : ℝ)^2 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ M-1 by linarith) (show 0 ≤ (ℓ : ℝ)^2-1 by linarith)]

theorem advertised_coefficient_budget (D ℓ : ℕ) (hD : 1 ≤ D)
    (M : ℝ) (hM : 1 ≤ M) :
    10*(ℓ : ℝ)^2*M ≤ 10*(D : ℝ)^4*(ℓ : ℝ)^2*M^4 := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hD4 : 1 ≤ (D : ℝ)^4 := by nlinarith [sq_nonneg ((D : ℝ)^2-1)]
  have hM4 : M ≤ M^4 := by
    have hM2 : M ≤ M^2 := by nlinarith
    have hM2p : 1 ≤ M^2 := by nlinarith
    nlinarith [sq_nonneg (M^2-1)]
  have h1 := mul_le_mul_of_nonneg_left hM4 (show 0 ≤ 10*(ℓ : ℝ)^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hD4 (show 0 ≤ 10*(ℓ : ℝ)^2*M^4 by positivity)
  nlinarith

#print axioms realization_M_at_least_one
#print axioms realization_M_at_least_support
#print axioms realization_M_reciprocal_control
#print axioms schedule_matrix_factor_bound
#print axioms selector_coefficient_budget
#print axioms advertised_coefficient_budget
end GeneralizationCheck
