module

public import ICLGeneralization.NetworkPolynomial

@[expose] public section
namespace GeneralizationCheck

def coverPolynomialDegree : ℕ := networkPolynomialDegree 5+16

theorem cover_constant_polynomial_majorant (D w m ℓ : ℕ) (κ R b s0 U T : ℝ)
    (hT : 2≤T) (hκ : 0≤κ) (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0) (hU : 0≤U)
    (hD : (D:ℝ)≤T) (hw : (w:ℝ)≤T) (hm : (m:ℝ)≤T) (hl : (ℓ:ℝ)≤T)
    (hk : κ≤T) (hr : R≤T) (hbb : b≤T) (ht : scheduleFactor s0≤T) (hu : U≤T) :
    verifiedLossCoverConstant D w m ℓ 6 5 κ R b s0 U≤T^coverPolynomialDegree := by
  have hT0 : 0≤T := by linarith
  have hT1 : 1≤T := by linarith
  unfold coverPolynomialDegree
  generalize hp : networkPolynomialDegree 5 = p
  have hn := network_polynomial_majorant D w m ℓ κ s0 U T hT hκ hs0 hU hD hw hm hl hk ht hu 5
  rw [hp] at hn
  have hn0 := network_bounds_nonnegative D w m ℓ 6 κ s0 U hκ hs0 hU 5
  have hNR : networkRadius D w m ℓ 6 κ s0 U 5≤T^p := hn.1
  have hNS : networkSensitivity D w m ℓ 6 κ s0 U 5≤T^p := hn.2
  have hRnonneg := hn0.1
  have hCnonneg := hn0.2
  have hV : 1≤T^p := one_le_pow₀ hT1
  have hnet : transformerSensitivity D w m ℓ 6 5 κ s0 U≤T^(p+3) := by
    unfold transformerSensitivity
    calc
      _≤T*(T^p+T*T^p) := by gcongr
      _=(T+T^2)*T^p := by ring
      _≤T^3*T^p := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [sq_nonneg (T-2)]
      _=T^(p+3) := by rw [←pow_add]; congr 1; omega
  have hrec : 1/s0≤T := by unfold scheduleFactor at ht; linarith
  have hsum : R+b≤2*T := by linarith
  have h4 : 4≤T^2 := by nlinarith [sq_nonneg (T-2)]
  have hM : lossEnvelope D R b s0≤T^9 := by
    have he : lossEnvelope D R b s0=(D:ℝ)*(R+b)^2*(1/s0)^4 := by unfold lossEnvelope; ring
    rw [he]
    calc
      _≤T*(2*T)^2*T^4 := by gcongr
      _=4*T^7 := by ring
      _≤T^2*T^7 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=T^9 := by ring
  have hconv : lossConversion D R b s0≤T^8 := by
    have he : lossConversion D R b s0=2*(D:ℝ)*(R+b)*(1/s0)^4 := by unfold lossConversion; ring
    rw [he]
    calc
      _≤2*T*(2*T)*T^4 := by gcongr
      _=4*T^6 := by ring
      _≤T^2*T^6 := mul_le_mul_of_nonneg_right h4 (by positivity)
      _=T^8 := by ring
  have hsens : lossSensitivity D w m ℓ 6 5 κ R b s0 U≤T^(p+11) := by
    unfold lossSensitivity
    have hconv0 : 0≤lossConversion D R b s0 := by unfold lossConversion; positivity
    have hnet0 : 0≤transformerSensitivity D w m ℓ 6 5 κ s0 U := by
      unfold transformerSensitivity
      exact mul_nonneg (by positivity) (add_nonneg hn0.1 (mul_nonneg hκ hn0.2))
    calc
      _≤T^8*T^(p+3) := by gcongr
      _=T^(p+11) := by rw [←pow_add]; congr 1; omega
  have hV1 : 1≤T^(p+11) := one_le_pow₀ hT1
  have h9 : T^9≤T^(p+12) := pow_le_pow_right₀ hT1 (by omega)
  have h16 : 10≤T^4 := by nlinarith [sq_nonneg (T^2-2)]
  have hsens0 := loss_sensitivity_nonnegative D w m ℓ 6 5 κ R b s0 U hκ hR hb hs0 hU
  unfold verifiedLossCoverConstant entropyRadius
  calc
    _≤4*T*(T^(p+11)+1)+2*T^9 := by gcongr
    _≤4*T*(2*T^(p+11))+2*T^(p+12) := by gcongr; linarith
    _=10*T^(p+12) := by rw [pow_add,pow_add]; ring
    _≤T^4*T^(p+12) := mul_le_mul_of_nonneg_right h16 (by positivity)
    _=T^(p+16) := by rw [←pow_add]; congr 1; omega

#print axioms cover_constant_polynomial_majorant
end GeneralizationCheck
