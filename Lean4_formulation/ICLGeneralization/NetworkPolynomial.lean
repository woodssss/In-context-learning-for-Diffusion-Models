module

public import ICLGeneralization.FullLossMeasurability

@[expose] public section
namespace GeneralizationCheck

theorem polynomial_scale_sum (T : ℝ) (hT : 2≤T) : T+1+T^2≤T^4 := by
  nlinarith [sq_nonneg (T^2-2),sq_nonneg (T-2)]

theorem ffn_polynomial_majorant (w : ℕ) (κ B C T : ℝ) (hT : 2≤T) (hκ : 0≤κ)
    (hw : (w:ℝ)≤T) (hk : κ≤T) (hB : 0≤B) (hC : 0≤C)
    (hBT : B≤T^20) (hCT : C≤T^20) (j : ℕ) :
    ffnRadius w κ B j≤T^(20+4*j) ∧ ffnSensitivity w κ B C j≤T^(20+4*j) := by
  have hT0 : 0≤T := by linarith
  have hT1 : 1≤T := by linarith
  induction j with
  | zero => simpa only [Nat.mul_zero,Nat.add_zero,ffnRadius,ffnSensitivity] using And.intro hBT hCT
  | succ j ih =>
    let a := 20+4*j
    have hV1 : 1≤T^a := one_le_pow₀ hT1
    have hVT : T≤T^a := by
      simpa only [pow_one] using pow_le_pow_right₀ hT1 (show 1≤a by dsimp [a]; omega)
    have hiR : ffnRadius w κ B j≤T^a := ih.1
    have hiC : ffnSensitivity w κ B C j≤T^a := ih.2
    have hffR0 := ffn_radius_nonnegative w κ B hκ hB j
    have hffC0 := ffn_sensitivity_nonnegative w κ B C hκ hB hC j
    have hR : κ+(w:ℝ)*κ*ffnRadius w κ B j≤T+(T*T)*T^a := by gcongr
    have hC' : (w:ℝ)*ffnRadius w κ B j+1+(w:ℝ)*κ*ffnSensitivity w κ B C j≤T*T^a+1+(T*T)*T^a := by gcongr
    have hcoef := polynomial_scale_sum T hT
    have hnext : T^(20+4*(j+1))=T^4*T^a := by dsimp [a]; rw [←pow_add]; congr 1; omega
    constructor
    · rw [ffnRadius,hnext]
      calc
        _≤T+(T*T)*T^a := hR
        _≤(T+1+T^2)*T^a := by nlinarith
        _≤T^4*T^a := mul_le_mul_of_nonneg_right hcoef (by positivity)
    · rw [ffnSensitivity,hnext]
      calc
        _≤T*T^a+1+(T*T)*T^a := hC'
        _≤(T+1+T^2)*T^a := by nlinarith
        _≤T^4*T^a := mul_le_mul_of_nonneg_right hcoef (by positivity)

theorem block_polynomial_majorant (w m ℓ : ℕ) (κ s0 B C T : ℝ)
    (hT : 2≤T) (hκ : 0≤κ) (hs0 : 0<s0) (hB : 0≤B) (hC : 0≤C)
    (hw : (w:ℝ)≤T) (hm : (m:ℝ)≤T) (hl : (ℓ:ℝ)≤T) (hk : κ≤T)
    (ht : scheduleFactor s0≤T) (hBT : B≤T) (hCT : C≤T) :
    blockRadius w m ℓ 6 κ s0 B≤T^50 ∧ blockSensitivity w m ℓ 6 κ s0 B C≤T^50 := by
  have hT0 : 0≤T := by linarith
  have hT1 : 1≤T := by linarith
  have ht0 : 0≤scheduleFactor s0 := by unfold scheduleFactor; positivity
  have hq0 := projection_radius_nonnegative w κ s0 B hκ hs0 hB
  have he0 := projection_sensitivity_nonnegative w κ s0 B C hκ hs0 hB hC
  have hq : projectionRadius w κ s0 B≤T^4 := by unfold projectionRadius; calc
    _≤T*(T*T)*T := by gcongr
    _=T^4 := by ring
  have he : projectionSensitivity w κ s0 B C≤T^5 := by
    unfold projectionSensitivity
    calc
      _≤T*(T*T+T*T*T) := by gcongr
      _≤T^5 := by nlinarith [sq_nonneg (T-2),sq_nonneg (T^2-2)]
  have ha0 := mha_radius_nonnegative w m ℓ κ s0 B hκ hs0 hB
  have hc0 := mha_sensitivity_nonnegative w m ℓ κ s0 B C hκ hs0 hB hC
  have ha : mhaRadius w m ℓ κ s0 B≤T^16 := by
    unfold mhaRadius
    calc
      _≤T*(T^4+T*T*(T^4)^3) := by gcongr
      _=T^5+T^15 := by ring
      _≤T^16 := by
        have h5 : T^5≤T^15 := pow_le_pow_right₀ hT1 (by decide)
        have hh := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 15)
        rw [←pow_succ'] at hh
        norm_num only at hh
        linarith
  have hc : mhaSensitivity w m ℓ κ s0 B C≤T^19 := by
    unfold mhaSensitivity
    calc
      _≤T*(1+4*T*(T^4)^2+3*T*T*(T^4)^2)*T^5 := by gcongr
      _=T^6+4*T^15+3*T^16 := by ring
      _≤8*T^16 := by
        have h6 : T^6≤T^16 := pow_le_pow_right₀ hT1 (by decide)
        have h15 : T^15≤T^16 := pow_le_pow_right₀ hT1 (by decide)
        linarith
      _≤T^19 := by
        have hh : 8≤T^3 := by nlinarith [sq_nonneg (T-2)]
        have hmul := mul_le_mul_of_nonneg_right hh (pow_nonneg hT0 16)
        simpa only [←pow_add] using hmul
  have hz : B+mhaRadius w m ℓ κ s0 B≤T^20 := by
    have h16 : T^16≤T^19 := pow_le_pow_right₀ hT1 (by decide)
    have h1 : T≤T^19 := by simpa only [pow_one] using pow_le_pow_right₀ hT1 (show 1≤19 by decide)
    have hmul := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 19)
    rw [←pow_succ'] at hmul
    norm_num only at hmul
    linarith
  have hd : C+mhaSensitivity w m ℓ κ s0 B C≤T^20 := by
    have h1 : T≤T^19 := by simpa only [pow_one] using pow_le_pow_right₀ hT1 (show 1≤19 by decide)
    have hmul := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 19)
    rw [←pow_succ'] at hmul
    norm_num only at hmul
    linarith
  have hz0 := add_nonneg hB ha0
  have hd0 := add_nonneg hC hc0
  have hff := ffn_polynomial_majorant w κ _ _ T hT hκ hw hk hz0 hd0 hz hd 6
  have h20 : T^20≤T^44 := pow_le_pow_right₀ hT1 (by decide)
  have hh := mul_le_mul_of_nonneg_right hT (pow_nonneg hT0 44)
  have h45 : T^45≤T^50 := pow_le_pow_right₀ hT1 (by decide)
  rw [←pow_succ'] at hh
  norm_num only at hh
  constructor
  · unfold blockRadius
    dsimp only
    norm_num only at hff
    nlinarith [hff.1]
  · unfold blockSensitivity
    dsimp only
    norm_num only at hff
    nlinarith [hff.2]

def networkPolynomialDegree : ℕ → ℕ
  | 0 => 4
  | j+1 => 50*(1+networkPolynomialDegree j)

theorem network_polynomial_degree_positive (j : ℕ) : 1≤networkPolynomialDegree j := by
  induction j with
  | zero => decide
  | succ j ih => simp only [networkPolynomialDegree]; omega

theorem network_polynomial_majorant (D w m ℓ : ℕ) (κ s0 U T : ℝ)
    (hT : 2≤T) (hκ : 0≤κ) (hs0 : 0<s0) (hU : 0≤U)
    (hD : (D:ℝ)≤T) (hw : (w:ℝ)≤T) (hm : (m:ℝ)≤T) (hl : (ℓ:ℝ)≤T)
    (hk : κ≤T) (ht : scheduleFactor s0≤T) (hu : U≤T) (j : ℕ) :
    networkRadius D w m ℓ 6 κ s0 U j≤T^(networkPolynomialDegree j) ∧
    networkSensitivity D w m ℓ 6 κ s0 U j≤T^(networkPolynomialDegree j) := by
  have hT0 : 0≤T := by linarith
  have hT1 : 1≤T := by linarith
  induction j with
  | zero =>
    simp only [networkRadius,networkSensitivity,networkPolynomialDegree]
    have hR : 1+(D:ℝ)*κ*U≤1+T*T*T := by gcongr
    have hC : (D:ℝ)*U≤T*T := by gcongr
    constructor <;> nlinarith [sq_nonneg (T^2-2),sq_nonneg (T-2)]
  | succ j ih =>
    let a := networkPolynomialDegree j
    let S := T^(a+1)
    have hTS : T≤S := by simpa only [pow_one] using pow_le_pow_right₀ hT1 (show 1≤a+1 by omega)
    have hS : 2≤S := hT.trans hTS
    have hV : T^a≤S := pow_le_pow_right₀ hT1 (by omega)
    have hnonneg := network_bounds_nonnegative D w m ℓ 6 κ s0 U hκ hs0 hU j
    have h := block_polynomial_majorant w m ℓ κ s0 _ _ S hS hκ hs0 hnonneg.1 hnonneg.2
      (hw.trans hTS) (hm.trans hTS) (hl.trans hTS) (hk.trans hTS) (ht.trans hTS)
      (ih.1.trans hV) (ih.2.trans hV)
    have he : S^50=T^(networkPolynomialDegree (j+1)) := by
      dsimp [S,a]
      rw [←pow_mul,networkPolynomialDegree]
      congr 1
      omega
    rw [he] at h
    exact h

#print axioms network_polynomial_degree_positive
#print axioms network_polynomial_majorant

#print axioms polynomial_scale_sum
#print axioms ffn_polynomial_majorant
#print axioms block_polynomial_majorant
end GeneralizationCheck
