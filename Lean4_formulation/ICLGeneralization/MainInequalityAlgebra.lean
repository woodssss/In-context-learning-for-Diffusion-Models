module

public import ICLGeneralization.MainTheorem

@[expose] public section
namespace GeneralizationCheck

noncomputable def mainInequalityStatisticalConstant (b R : ℝ) : ℝ :=
  (statisticalRateConstant 41943040 b R+Real.sqrt 3)*(R+b)^2

noncomputable def mainInequalityApproximationConstant (b R A : ℝ) (d : ℕ) : ℝ :=
  approximationConstant b d*A+4*b^2+7*(R+b)^2

theorem cutoff_strictly_less_than_one (n d : ℕ) (hn : 2≤n) :
    (n:ℝ)^(-1/((d:ℝ)+6))<1 := by
  have hn1 : (1:ℝ)<n := by exact_mod_cast (show 1<n by omega)
  exact Real.rpow_lt_one_of_one_lt_of_neg hn1 (div_neg_of_neg_of_pos (by norm_num) (by positivity))

theorem lemma_three_sigma_six_algebra (D K J N : ℕ) (b R s0 : ℝ) (hs0 : 0<s0) :
    lossEnvelope D R b s0*Real.sqrt (Real.log (1/s0^6)/2)*hierarchicalSamplingFactor K J N+
      6*s0^6*lossEnvelope D R b s0 =
    lossEnvelope D R b s0*Real.sqrt (3*Real.log (1/s0))*hierarchicalSamplingFactor K J N+
      6*(D:ℝ)*(R+b)^2*s0^2 := by
  have hlog : Real.log (1/s0^6)/2=3*Real.log (1/s0) := by
    rw [one_div,Real.log_inv,Real.log_pow,one_div,Real.log_inv]
    norm_num
    ring
  rw [hlog]
  have he : 6*s0^6*lossEnvelope D R b s0=6*(D:ℝ)*(R+b)^2*s0^2 := by
    unfold lossEnvelope
    field_simp
  rw [he]

theorem lemma_three_sigma_six_absorbed (n D K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (b R s0 : ℝ) (hs0 : 0<s0) (hs1 : s0≤1) :
    lossEnvelope D R b s0*Real.sqrt (Real.log (1/s0^6)/2)*hierarchicalSamplingFactor K J N+
      6*s0^6*lossEnvelope D R b s0 ≤
    Real.sqrt 3*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      6*(D:ℝ)*(R+b)^2*s0^2 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have hT1 : (1:ℝ)≤((K*J)*N:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Nat.mul_pos (Nat.mul_pos hK hJ) hN))
  have hprod : 1≤(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hn1 hD1) hT1
  have harg : 1/s0≤(n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0 :=
    div_le_div_of_nonneg_right hprod hs0.le
  have hlog := Real.log_le_log (show 0<1/s0 by positivity) harg
  have hlog0 : 0≤Real.log (1/s0) := Real.log_nonneg ((le_div_iff₀ hs0).mpr (by simpa only [one_mul] using hs1))
  have hlogB : 0≤Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0) := hlog0.trans hlog
  have hscale : 1≤(n:ℝ)*(D:ℝ)^3 := one_le_mul_of_one_le_of_one_le hn1 (one_le_pow₀ hD1)
  have hlogScale : Real.log (1/s0)≤(n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0) :=
    hlog.trans (by nlinarith only [mul_nonneg (sub_nonneg.mpr hscale) hlogB])
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlogScale (by norm_num : (0:ℝ)≤3))
  conv_rhs at hsqrt => rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤3)]
  have hM : 0≤lossEnvelope D R b s0 := by unfold lossEnvelope; positivity
  have hΦ : 0≤hierarchicalSamplingFactor K J N := by unfold hierarchicalSamplingFactor; positivity
  rw [lemma_three_sigma_six_algebra D K J N b R s0 hs0]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hM) hΦ
  exact add_le_add (by convert h using 1; ring) (le_refl _)

theorem main_bound_cutoff_inequality (n D d K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (b R A : ℝ) :
    let s0 := (n:ℝ)^(-1/((d:ℝ)+6))
    (statisticalRateConstant 41943040 b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2)+
    (lossEnvelope D R b s0*Real.sqrt (Real.log (1/s0^6)/2)*hierarchicalSamplingFactor K J N+
      6*s0^6*lossEnvelope D R b s0)+
    (approximationConstant b d*A*(D:ℝ)/((n:ℝ)*s0^(d+4))+4*(D:ℝ)*b^2*s0^2) ≤
    mainInequalityStatisticalConstant b R*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*
      Real.sqrt (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N+
      mainInequalityApproximationConstant b R A d*(D:ℝ)*(n:ℝ)^(-2/((d:ℝ)+6)) := by
  dsimp only
  let s0 := (n:ℝ)^(-1/((d:ℝ)+6))
  have hs := cutoff_positive_and_le_one n d (by omega)
  have hbase := main_bound_cutoff n D d K J N hn hD hK hJ hN b R A
  have hII := lemma_three_sigma_six_absorbed n D K J N hn hD hK hJ hN b R s0 hs.1 hs.2
  have hlog := cutoff_log_bound n D d K J N hn hD hK hJ hN
  have hΦ : 0≤hierarchicalSamplingFactor K J N := by unfold hierarchicalSamplingFactor; positivity
  have hM : 0≤Real.sqrt 3*lossEnvelope D R b s0 := by unfold lossEnvelope; positivity
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hlog (show 0≤(n:ℝ)*(D:ℝ)^3 by positivity))
  have hII' := hII.trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hM) hΦ) (le_refl _))
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hscale := statistical_cutoff_scaling n D d (by omega) hD b R
    (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))
  have he : Real.sqrt 3*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N =
      Real.sqrt 3*((R+b)^2*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*
        Real.sqrt (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ))))*hierarchicalSamplingFactor K J N := by
    rw [mul_assoc (Real.sqrt 3),hscale]
  rw [he,cutoff_squared (n:ℝ) (d:ℝ) hn0] at hII'
  have hout := add_le_add hbase hII'
  convert hout using 1
  · ring
  · unfold mainInequalityStatisticalConstant mainInequalityApproximationConstant mainStatisticalConstant mainApproximationConstant
    ring

#print axioms cutoff_strictly_less_than_one
#print axioms lemma_three_sigma_six_algebra
#print axioms lemma_three_sigma_six_absorbed
#print axioms main_bound_cutoff_inequality
end GeneralizationCheck
