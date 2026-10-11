module

public import ICLGeneralization.StatisticalBudgetScale

@[expose] public section
namespace GeneralizationCheck

noncomputable def statisticalLogConstant (cκ b R : ℝ) : ℝ :=
  (coverPolynomialDegree:ℝ)*Real.log (statisticalScaleConstant cκ b R)/Real.log 2+
    8*(coverPolynomialDegree:ℝ)+1

theorem statistical_cover_log_bound (n D K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (κ cκ b R s0 : ℝ)
    (hκ : 0≤κ) (hcκ : 0≤cκ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (hk : κ≤cκ*(D:ℝ)^8*(n:ℝ)^2*b^8*R^4/s0^8) :
    Real.log (verifiedLossCoverConstant D (2*D+6) n (n+1) 6 5 κ R b s0 (max 1 (b+noiseRadius D s0))*
      Real.sqrt ((K*J)*N:ℝ)/lossEnvelope D R b s0) ≤
      statisticalLogConstant cκ b R*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0) := by
  let x := statisticalScale n D s0
  let C := statisticalScaleConstant cκ b R
  let B := verifiedLossCoverConstant D (2*D+6) n (n+1) 6 5 κ R b s0 (max 1 (b+noiseRadius D s0))
  let M := lossEnvelope D R b s0
  let Z : ℝ := ((K*J)*N:ℝ)
  let p := coverPolynomialDegree
  have hn1 : 1≤n := by omega
  obtain ⟨hT,hDb,hw,hm,hl,hkb,hr,hbb,ht,hu⟩ := statistical_budget_scale n D hn1 hD κ cκ b R s0 hκ hcκ hb hR hs0 hs1 hk
  have hxge : 2≤x := by
    have hnR : 2≤(n:ℝ) := by exact_mod_cast hn
    have hDR : 1≤(D:ℝ) := by exact_mod_cast hD
    have hnu : 1≤1/s0 := (le_div_iff₀ hs0).mpr (by simpa only [one_mul] using hs1)
    dsimp [x,statisticalScale]
    calc 2=2*1*1 := by ring
         _≤(n:ℝ)*(D:ℝ)*(1/s0) := by gcongr
         _=(n:ℝ)*(D:ℝ)/s0 := by ring
  have hxpos : 0<x := by linarith
  have hC : 16≤C := by
    dsimp [C,statisticalScaleConstant]
    have hm : 0≤cκ*b^8*R^4 := by positivity
    linarith
  have hCpos : 0<C := by linarith
  have hU : 0≤max 1 (b+noiseRadius D s0) := by positivity
  have hw' : ((2*D+6:ℕ):ℝ)≤statisticalScaleConstant cκ b R*(statisticalScale n D s0)^8 := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hw
  have hl' : ((n+1:ℕ):ℝ)≤statisticalScaleConstant cκ b R*(statisticalScale n D s0)^8 := by
    simpa only [Nat.cast_add,Nat.cast_one] using hl
  have hB := cover_constant_polynomial_majorant D (2*D+6) n (n+1) κ R b s0 _ _ hT hκ (by linarith)
    (by linarith) hs0 hU hDb hw' hm hl' hkb hr hbb ht hu
  change B≤(C*x^8)^p at hB
  have hM1 : 1≤M := by
    have hDR : 1≤(D:ℝ) := by exact_mod_cast hD
    have hsum : 1≤R+b := by linarith
    have hnu : 1≤1/s0 := (le_div_iff₀ hs0).mpr (by simpa only [one_mul] using hs1)
    have he : M=(D:ℝ)*(R+b)^2*(1/s0)^4 := by dsimp [M,lossEnvelope]; ring
    rw [he]
    calc 1=1*1^2*1^4 := by norm_num
         _≤(D:ℝ)*(R+b)^2*(1/s0)^4 := by gcongr
  have hMpos : 0<M := by linarith
  have hZ1 : 1≤Z := by dsimp [Z]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.mul_pos (Nat.mul_pos hK hJ) hN))
  have hZpos : 0<Z := by linarith
  have hSpos : 0<Real.sqrt Z := Real.sqrt_pos.mpr hZpos
  have hSle : Real.sqrt Z≤Z := by nlinarith [Real.sq_sqrt hZpos.le,Real.sqrt_nonneg Z]
  have hBpos : 0<B := by
    have hk0 := loss_sensitivity_nonnegative D (2*D+6) n (n+1) 6 5 κ R b s0 _ hκ (by linarith) (by linarith) hs0 hU
    dsimp [B,verifiedLossCoverConstant,entropyRadius]
    nlinarith
  have hratio : 0<B*Real.sqrt Z/M := by positivity
  have hupper : B*Real.sqrt Z/M≤(C*x^8)^p*Z := by
    calc
      _≤B*Real.sqrt Z := div_le_self (by positivity) hM1
      _≤(C*x^8)^p*Z := by gcongr
  have hlog := Real.log_le_log hratio hupper
  have hpoly : Real.log ((C*x^8)^p*Z) = (p:ℝ)*(Real.log C+8*Real.log x)+Real.log Z := by
    rw [Real.log_mul (by positivity) (ne_of_gt hZpos),Real.log_pow,Real.log_mul (ne_of_gt hCpos) (by positivity),Real.log_pow]
    norm_num
  rw [hpoly] at hlog
  have hyx : x≤x*Z := by nlinarith
  have hyZ : Z≤x*Z := by nlinarith
  have hlogx : Real.log x≤Real.log (x*Z) := Real.log_le_log hxpos hyx
  have hlogZ : Real.log Z≤Real.log (x*Z) := Real.log_le_log hZpos hyZ
  have hlog2 : Real.log 2≤Real.log (x*Z) := Real.log_le_log (by norm_num) (hxge.trans hyx)
  have hlogC : 0≤Real.log C := Real.log_nonneg (by linarith)
  have hlog2pos : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hConst : (p:ℝ)*Real.log C≤((p:ℝ)*Real.log C/Real.log 2)*Real.log (x*Z) := by
    have hmul := mul_le_mul_of_nonneg_left hlog2 (show 0≤(p:ℝ)*Real.log C/Real.log 2 by positivity)
    have he : ((p:ℝ)*Real.log C/Real.log 2)*Real.log 2=(p:ℝ)*Real.log C := by field_simp
    rwa [he] at hmul
  have hmid : (p:ℝ)*(Real.log C+8*Real.log x)+Real.log Z≤
      ((p:ℝ)*Real.log C/Real.log 2+8*(p:ℝ)+1)*Real.log (x*Z) := by
    have hh := mul_le_mul_of_nonneg_left hlogx (show 0≤8*(p:ℝ) by positivity)
    nlinarith only [hConst,hh,hlogZ]
  apply hlog.trans
  have he : x*Z=(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0 := by dsimp [x,statisticalScale,Z]; ring
  rw [he] at hmid
  simpa only [statisticalLogConstant,p,C] using hmid

#print axioms statistical_cover_log_bound
end GeneralizationCheck
