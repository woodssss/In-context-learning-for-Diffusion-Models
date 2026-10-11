module

public import ICLGeneralization.CoverPolynomial

@[expose] public section
namespace GeneralizationCheck

noncomputable def statisticalScaleConstant (cκ b R : ℝ) : ℝ := 16+cκ*b^8*R^4+b+R
noncomputable def statisticalScale (n D : ℕ) (s0 : ℝ) : ℝ := (n:ℝ)*(D:ℝ)/s0

theorem statistical_budget_scale (n D : ℕ) (hn : 1≤n) (hD : 1≤D)
    (κ cκ b R s0 : ℝ) (_hκ : 0≤κ) (hcκ : 0≤cκ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (hk : κ≤cκ*(D:ℝ)^8*(n:ℝ)^2*b^8*R^4/s0^8) :
    let T := statisticalScaleConstant cκ b R*(statisticalScale n D s0)^8
    2≤T ∧ (D:ℝ)≤T ∧ (2*D+6:ℝ)≤T ∧ (n:ℝ)≤T ∧ (n+1:ℝ)≤T ∧ κ≤T ∧
      R≤T ∧ b≤T ∧ scheduleFactor s0≤T ∧ max 1 (b+noiseRadius D s0)≤T := by
  dsimp only
  let x := statisticalScale n D s0
  let C := statisticalScaleConstant cκ b R
  have hnR : 1≤(n:ℝ) := by exact_mod_cast hn
  have hDR : 1≤(D:ℝ) := by exact_mod_cast hD
  have hb0 : 0≤b := by linarith
  have hR0 : 0≤R := by linarith
  have hnu : 1≤1/s0 := (le_div_iff₀ hs0).mpr (by simpa only [one_mul] using hs1)
  have hx : x=(n:ℝ)*(D:ℝ)*(1/s0) := by dsimp [x,statisticalScale]; ring
  have hn0 : 0≤(n:ℝ) := by positivity
  have hD0 : 0≤(D:ℝ) := by positivity
  have hnu0 : 0≤1/s0 := by positivity
  have hx1 : 1≤x := by
    rw [hx]
    calc 1=1*1*1 := by ring
         _≤(n:ℝ)*(D:ℝ)*(1/s0) := by gcongr
  have hxD : (D:ℝ)≤x := by
    rw [hx]
    calc (D:ℝ)=1*(D:ℝ)*1 := by ring
         _≤(n:ℝ)*(D:ℝ)*(1/s0) := by gcongr
  have hxn : (n:ℝ)≤x := by
    rw [hx]
    calc (n:ℝ)=(n:ℝ)*1*1 := by ring
         _≤(n:ℝ)*(D:ℝ)*(1/s0) := by gcongr
  have hxnu : 1/s0≤x := by
    rw [hx]
    calc 1/s0=1*1*(1/s0) := by ring
         _≤(n:ℝ)*(D:ℝ)*(1/s0) := by gcongr
  have hx0 : 0≤x := by linarith
  have hx8 : x≤x^8 := by simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1≤8 by decide)
  have hx81 : 1≤x^8 := one_le_pow₀ hx1
  have hmon : 0≤cκ*b^8*R^4 := by positivity
  have hC : 16≤C := by dsimp [C,statisticalScaleConstant]; linarith
  have hCR : R≤C := by dsimp [C,statisticalScaleConstant]; linarith
  have hCb : b≤C := by dsimp [C,statisticalScaleConstant]; linarith
  have hCκ : cκ*b^8*R^4≤C := by dsimp [C,statisticalScaleConstant]; linarith
  have hC6 : b+6≤C := by dsimp [C,statisticalScaleConstant]; linarith
  have hC0 : 0≤C := by linarith
  have hTC : C≤C*x^8 := by
    have hh := mul_le_mul_of_nonneg_left hx81 hC0
    simpa only [mul_one] using hh
  have hxT : x^8≤C*x^8 := by
    have hh := mul_le_mul_of_nonneg_right (show 1≤C by linarith) (pow_nonneg hx0 8)
    simpa only [one_mul] using hh
  have h8 : 8*x≤C*x^8 := mul_le_mul (by linarith) hx8 hx0 hC0
  have hT : 16≤C*x^8 := hC.trans hTC
  have hD8 : (D:ℝ)≤C*x^8 := hxD.trans (hx8.trans hxT)
  have hw8 : (2*D+6:ℝ)≤C*x^8 := (show (2*D+6:ℝ)≤8*x by linarith).trans h8
  have hn8 : (n:ℝ)≤C*x^8 := hxn.trans (hx8.trans hxT)
  have hℓ8 : (n+1:ℝ)≤C*x^8 := (show (n+1:ℝ)≤8*x by linarith).trans h8
  have hnn : (n:ℝ)^2≤(n:ℝ)^8 := pow_le_pow_right₀ hnR (by decide)
  have hkx : κ≤(cκ*b^8*R^4)*x^8 := by
    apply hk.trans
    rw [hx]
    calc
      _=(cκ*b^8*R^4)*(n:ℝ)^2*(D:ℝ)^8*(1/s0)^8 := by ring
      _≤(cκ*b^8*R^4)*(n:ℝ)^8*(D:ℝ)^8*(1/s0)^8 := by gcongr
      _=(cκ*b^8*R^4)*((n:ℝ)*(D:ℝ)*(1/s0))^8 := by ring
  have hκT : κ≤C*x^8 := hkx.trans (mul_le_mul_of_nonneg_right hCκ (by positivity))
  have hRT : R≤C*x^8 := hCR.trans hTC
  have hbT : b≤C*x^8 := hCb.trans hTC
  have hτT : scheduleFactor s0≤C*x^8 := (show scheduleFactor s0≤8*x by unfold scheduleFactor; linarith).trans h8
  have hradius := logarithmic_radius_bound D s0 hs0 hs1
  have hrad0 := noise_radius_nonnegative D s0
  have hx2 : x≤x^2 := by simpa only [pow_one] using pow_le_pow_right₀ hx1 (show 1≤2 by decide)
  have hnu2 : (1/s0)^2≤x^2 := pow_le_pow_left₀ hnu0 hxnu 2
  have hD2 : (D:ℝ)≤x^2 := hxD.trans hx2
  have he : 24/s0^2=24*(1/s0)^2 := by ring
  rw [he] at hradius
  have hrx : noiseRadius D s0≤6*x := by nlinarith
  have hbplus : b+noiseRadius D s0≤(b+6)*x := by nlinarith [mul_le_mul_of_nonneg_left hx1 hb0]
  have hprod : (b+6)*x≤C*x^8 := mul_le_mul hC6 hx8 hx0 hC0
  have hUT : max 1 (b+noiseRadius D s0)≤C*x^8 := max_le (by linarith) (hbplus.trans hprod)
  exact ⟨by linarith,hD8,hw8,hn8,hℓ8,hκT,hRT,hbT,hτT,hUT⟩

#print axioms statistical_budget_scale
end GeneralizationCheck
