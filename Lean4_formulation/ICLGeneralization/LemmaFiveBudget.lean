module

public import ICLGeneralization.LemmaFiveScore

@[expose] public section

namespace GeneralizationCheck

theorem logarithmic_radius_bound (D : ℕ) (s0 : ℝ) (hs0 : 0 < s0) (hs1 : s0 ≤ 1) :
    (noiseRadius D s0)^2 ≤ 2*(D : ℝ)+24/s0^2 := by
  rw [noise_radius_squared D s0 hs0 hs1]
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : Real.log (1/s0) ≤ 1/s0^2 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1/s0 by positivity)
    have he : 1/s0^2=(1/s0)^2 := by ring
    rw [he]
    nlinarith [sq_nonneg (1/s0-1/2)]
  have h := mul_le_mul_of_nonneg_left hl2 (show 0 ≤ 2*(D : ℝ) by positivity)
  have hl := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 24)
  have he : 24*(1/s0^2)=24/s0^2 := by ring
  rw [he] at hl
  linarith

theorem lemma_five_realization_M_upper (D : ℕ) (hD : 1 ≤ D) (b R s0 : ℝ)
    (hb : 1 ≤ b) (hR : b ≤ R) (hs0 : 0 < s0) (hs1 : s0 ≤ 1) :
    realizationM D b R s0 (noiseRadius D s0) ≤ 32*(D : ℝ)*b^2*R/s0^2 := by
  have hDr : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  have hb2 : 1 ≤ b^2 := by nlinarith
  have hR1 : 1 ≤ R := hb.trans hR
  have hs2 : s0^2 ≤ 1 := by nlinarith
  let P := (D : ℝ)*b^2*R
  have hDb : 1 ≤ (D : ℝ)*b^2 := by nlinarith [mul_nonneg (show 0 ≤ (D : ℝ)-1 by linarith) (show 0 ≤ b^2-1 by linarith)]
  have hPDb : (D : ℝ)*b^2 ≤ P := by
    exact le_mul_of_one_le_right (by positivity) hR1
  have hPR : R ≤ P := by
    exact le_mul_of_one_le_left (by linarith : 0 ≤ R) hDb
  have hPD : (D : ℝ) ≤ P := (le_mul_of_one_le_right (by positivity) hb2).trans hPDb
  have hP1 : 1 ≤ P := hDb.trans hPDb
  have hPinv : P ≤ P/s0^2 := (le_div_iff₀ (sq_pos_of_pos hs0)).2
    (mul_le_of_le_one_right (by linarith : 0 ≤ P) hs2)
  have hbig : 0 ≤ P/s0^2 := by positivity
  have hroot : (2*b*Real.sqrt (D : ℝ)/s0)^2 = 4*(D : ℝ)*b^2/s0^2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hN := logarithmic_radius_bound D s0 hs0 hs1
  have h1inv : 1/s0^2 ≤ P/s0^2 := div_le_div_of_nonneg_right hP1 (by positivity)
  have hDbdiv : (D : ℝ)*b^2/s0^2 ≤ P/s0^2 := div_le_div_of_nonneg_right hPDb (by positivity)
  have he : 32*(D : ℝ)*b^2*R/s0^2 = 32*(P/s0^2) := by dsimp [P]; ring
  rw [he]
  unfold realizationM
  apply max_le
  · exact max_le (by nlinarith [hP1.trans hPinv]) (by nlinarith [hPR.trans hPinv])
  · have hsquare : (2*b*Real.sqrt (D : ℝ)/s0+noiseRadius D s0)^2/2 ≤
        (2*b*Real.sqrt (D : ℝ)/s0)^2+(noiseRadius D s0)^2 := by
      nlinarith [sq_nonneg (2*b*Real.sqrt (D : ℝ)/s0-noiseRadius D s0)]
    rw [hroot] at hsquare
    have hDdiv := hPD.trans hPinv
    have hcoef : 4*(D : ℝ)*b^2/s0^2 ≤ 4*(P/s0^2) := by
      have h := mul_le_mul_of_nonneg_left hDbdiv (by norm_num : (0 : ℝ) ≤ 4)
      convert h using 1
      ring
    have h24 : 24/s0^2 ≤ 24*(P/s0^2) := by
      have h := mul_le_mul_of_nonneg_left h1inv (by norm_num : (0 : ℝ) ≤ 24)
      convert h using 1
      ring
    linarith

theorem lemma_five_weight_budget_order (n D : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (b R s0 : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (hs0 : 0 < s0) (hs1 : s0 ≤ 1) :
    lemmaOneBudget n D (realizationM D b R s0 (noiseRadius D s0)) ≤
      41943040*(D : ℝ)^8*(n : ℝ)^2*b^8*R^4/s0^8 := by
  let M := realizationM D b R s0 (noiseRadius D s0)
  let U := 32*(D : ℝ)*b^2*R/s0^2
  have hM : 0 ≤ M := realization_M_nonnegative _ _ _ _ _
  have hMU : M ≤ U := lemma_five_realization_M_upper D hD b R s0 hb hR hs0 hs1
  have hpow : M^4 ≤ U^4 := pow_le_pow_left₀ hM hMU 4
  have hnr : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hℓ : (n+1 : ℝ)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
  unfold lemmaOneBudget
  calc
    _ ≤ 10*(D : ℝ)^4*(n+1 : ℝ)^2*U^4 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 10*(D : ℝ)^4*U^4*(n+1 : ℝ)^2 := by ring
    _ ≤ 10*(D : ℝ)^4*U^4*(4*(n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hℓ (by positivity)
    _ = _ := by
      dsimp only [U]
      simp only [div_pow, mul_pow]
      ring

#print axioms logarithmic_radius_bound
#print axioms lemma_five_realization_M_upper
#print axioms lemma_five_weight_budget_order
end GeneralizationCheck
