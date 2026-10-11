module

public import ICLGeneralization.StatisticalLogBound
public import ICLGeneralization.LemmaTwoGaussian

@[expose] public section
namespace GeneralizationCheck

noncomputable def statisticalRateConstant (cκ b R : ℝ) : ℝ :=
  4*(6*Real.sqrt (3136*statisticalLogConstant cκ b R)+1)

theorem statistical_log_constant_positive (cκ b R : ℝ) (hcκ : 0≤cκ) (hb : 1≤b) (hR : b≤R) :
    0<statisticalLogConstant cκ b R := by
  have hC : 1≤statisticalScaleConstant cκ b R := by
    unfold statisticalScaleConstant
    have h : 0≤cκ*b^8*R^4 := by positivity
    linarith
  have hlog : 0≤Real.log (statisticalScaleConstant cκ b R) := Real.log_nonneg hC
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold statisticalLogConstant
  positivity

theorem statistical_rate_constant_positive (cκ b R : ℝ) : 0<statisticalRateConstant cκ b R := by
  unfold statisticalRateConstant
  positivity

theorem lemma_two_bound_rate (n D K J N : ℕ) (hn : 2≤n) (hD : 1≤D) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (κ cκ b R s0 : ℝ) (hκ : 0≤κ) (hcκ : 0≤cκ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (hk : κ≤cκ*(D:ℝ)^8*(n:ℝ)^2*b^8*R^4/s0^8) :
    let B := verifiedLossCoverConstant D (2*D+6) n (n+1) 6 5 κ R b s0 (max 1 (b+noiseRadius D s0))
    let M := lossEnvelope D R b s0
    4*M*hierarchicalSamplingFactor K J N*
      (6*Real.sqrt ((D*fixedTimeParameterCount D (2*D+6) 5 6 n:ℝ)*Real.log (B*Real.sqrt ((K*J)*N:ℝ)/M))+1)+
      M*(gaussianNoiseLaw D {eps | noiseRadius D s0<‖eps‖}).toReal ≤
    statisticalRateConstant cκ b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2 := by
  dsimp only
  let B := verifiedLossCoverConstant D (2*D+6) n (n+1) 6 5 κ R b s0 (max 1 (b+noiseRadius D s0))
  let M := lossEnvelope D R b s0
  let P := D*fixedTimeParameterCount D (2*D+6) 5 6 n
  let c := statisticalLogConstant cκ b R
  let V := (n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0)
  let H := (P:ℝ)*Real.log (B*Real.sqrt ((K*J)*N:ℝ)/M)
  have hc : 0<c := statistical_log_constant_positive cκ b R hcκ hb hR
  have hlog := statistical_cover_log_bound n D K J N hn hD hK hJ hN κ cκ b R s0 hκ hcκ hb hR hs0 hs1 hk
  have hP : (P:ℝ)≤3136*(n:ℝ)*(D:ℝ)^3 := by
    exact_mod_cast fixed_concrete_vector_parameter_budget n D (by omega) hD
  have hZ1 : 1≤((K*J)*N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.mul_pos (Nat.mul_pos hK hJ) hN))
  have hn2 : 2≤(n:ℝ) := by exact_mod_cast hn
  have hD1 : 1≤(D:ℝ) := by exact_mod_cast hD
  have hnu : 1≤1/s0 := (le_div_iff₀ hs0).mpr (by simpa only [one_mul] using hs1)
  have hy2 : 2≤(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0 := by
    calc 2=2*1*1*1 := by ring
         _≤(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)*(1/s0) := by gcongr
         _=(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0 := by ring
  have hlog2 : 1/2≤Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  have hly : 1/2≤Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0) :=
    hlog2.trans (Real.log_le_log (by norm_num) hy2)
  have hV1 : 1≤V := by
    have hD3 : 1≤(D:ℝ)^3 := one_le_pow₀ hD1
    dsimp [V]
    calc 1=2*1*(1/2:ℝ) := by norm_num
         _≤(n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0) := by gcongr
  have hH : H≤(3136*c)*V := by
    dsimp [H]
    calc
      _≤(P:ℝ)*(c*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _≤(3136*(n:ℝ)*(D:ℝ)^3)*(c*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0)) := by
        apply mul_le_mul_of_nonneg_right hP
        positivity
      _=(3136*c)*V := by dsimp [V]; ring
  have hsqrt := Real.sqrt_le_sqrt hH
  rw [Real.sqrt_mul (by positivity : 0≤3136*c)] at hsqrt
  have hsqrt1 : 1≤Real.sqrt V := by nlinarith [Real.sq_sqrt (show 0≤V by linarith),Real.sqrt_nonneg V]
  have hfactor : 6*Real.sqrt H+1≤(6*Real.sqrt (3136*c)+1)*Real.sqrt V := by nlinarith
  have hM : 0≤M := by dsimp [M,lossEnvelope]; positivity
  have hfac : 0≤hierarchicalSamplingFactor K J N := by unfold hierarchicalSamplingFactor; positivity
  have hstat := mul_le_mul_of_nonneg_left hfactor (show 0≤4*M*hierarchicalSamplingFactor K J N by positivity)
  have htail := tail_remainder s0 (gaussianNoiseLaw D {eps | noiseRadius D s0<‖eps‖}).toReal
    ((D:ℝ)*(R+b)^2) hs0 (by positivity) (gaussian_tail_at_noise_radius D s0 hs0 hs1)
  have hout := add_le_add hstat htail
  convert hout using 1
  · simp only [M,H,P,B,lossEnvelope,Nat.cast_mul]
  · dsimp [statisticalRateConstant,c,M,V]
    ring

#print axioms statistical_log_constant_positive
#print axioms statistical_rate_constant_positive
#print axioms lemma_two_bound_rate
end GeneralizationCheck
