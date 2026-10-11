module

public import ICLGeneralization.StatisticalFinal

@[expose] public section
namespace GeneralizationCheck

noncomputable def mainStatisticalConstant (b R : ℝ) : ℝ :=
  statisticalRateConstant 41943040 b R*(R+b)^2

noncomputable def mainApproximationConstant (b R A : ℝ) (d : ℕ) : ℝ :=
  approximationConstant b d*A+4*b^2+(R+b)^2

theorem cutoff_positive_and_le_one (n d : ℕ) (hn : 1≤n) :
    0<(n:ℝ)^(-1/((d:ℝ)+6)) ∧ (n:ℝ)^(-1/((d:ℝ)+6))≤1 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hd : (0:ℝ)<(d:ℝ)+6 := by positivity
  have he : -1/((d:ℝ)+6)≤0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le
  exact ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos hn1 he⟩

theorem cutoff_log_bound (n D d K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) :
    Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/(n:ℝ)^(-1/((d:ℝ)+6)))≤
      Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hn0 : (0:ℝ)<n := by linarith
  have he : (n:ℝ)/(n:ℝ)^(-1/((d:ℝ)+6)) = (n:ℝ)^(1+1/((d:ℝ)+6)) := by
    conv_lhs => arg 1; rw [←Real.rpow_one (n:ℝ)]
    rw [←Real.rpow_sub hn0]
    congr 1
    ring
  have h := logarithm_simplification (n:ℝ) (d:ℝ) ((D:ℝ)*((K*J)*N:ℝ)) hn1 (by positivity)
    (by positivity)
  convert h using 1
  · congr 1
    rw [←he]
    ring
  · congr 1
    ring

theorem statistical_cutoff_scaling (n D d : ℕ) (hn : 0<n) (hD : 1≤D) (b R H : ℝ) :
    lossEnvelope D R b ((n:ℝ)^(-1/((d:ℝ)+6)))*Real.sqrt ((n:ℝ)*(D:ℝ)^3*H) =
      (R+b)^2*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*Real.sqrt H := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hD0 : (0:ℝ)<D := by exact_mod_cast (show 0<D by omega)
  rw [Real.sqrt_mul (show 0≤(n:ℝ)*(D:ℝ)^3 by positivity),Real.sqrt_mul (show 0≤(n:ℝ) by positivity)]
  have hdim := statistical_dimension_power (D:ℝ) hD0
  have hctx := statistical_context_power (n:ℝ) (d:ℝ) hn0
  unfold lossEnvelope
  calc
    _ = (R+b)^2*((D:ℝ)*Real.sqrt ((D:ℝ)^3))*(Real.sqrt (n:ℝ)/((n:ℝ)^(-1/((d:ℝ)+6)))^4)*Real.sqrt H := by ring
    _ = _ := by rw [hdim,hctx]

theorem main_bound_cutoff (n D d K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (b R A : ℝ) :
    let s0 := (n:ℝ)^(-1/((d:ℝ)+6))
    statisticalRateConstant 41943040 b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2+
      (approximationConstant b d*A*(D:ℝ)/((n:ℝ)*s0^(d+4))+4*(D:ℝ)*b^2*s0^2) ≤
    mainStatisticalConstant b R*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*
      Real.sqrt (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N+
      mainApproximationConstant b R A d*(D:ℝ)*(n:ℝ)^(-2/((d:ℝ)+6)) := by
  dsimp only
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hc := cutoff_squared (n:ℝ) (d:ℝ) hn0
  have ha := cutoff_approximation (n:ℝ) (d:ℝ) hn0 (by positivity)
  have hpow : ((n:ℝ)^(-1/((d:ℝ)+6)))^((d:ℝ)+4) = ((n:ℝ)^(-1/((d:ℝ)+6)))^(d+4) := by
    rw [show (d:ℝ)+4=((d+4:ℕ):ℝ) by norm_cast,Real.rpow_natCast]
  rw [hpow] at ha
  have hstat : statisticalRateConstant 41943040 b R*lossEnvelope D R b ((n:ℝ)^(-1/((d:ℝ)+6)))*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/(n:ℝ)^(-1/((d:ℝ)+6))))*hierarchicalSamplingFactor K J N ≤
      mainStatisticalConstant b R*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*
        Real.sqrt (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N := by
    calc
      _ ≤ statisticalRateConstant 41943040 b R*lossEnvelope D R b ((n:ℝ)^(-1/((d:ℝ)+6)))*
          Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N := by
        have hfac : 0≤hierarchicalSamplingFactor K J N := by unfold hierarchicalSamplingFactor; positivity
        have hcoef : 0≤statisticalRateConstant 41943040 b R*lossEnvelope D R b ((n:ℝ)^(-1/((d:ℝ)+6))) := by
          unfold statisticalRateConstant lossEnvelope
          positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
            (mul_le_mul_of_nonneg_left (cutoff_log_bound n D d K J N hn hD hK hJ hN) (by positivity))) hcoef) hfac
      _ = _ := by
        rw [mul_assoc (statisticalRateConstant 41943040 b R),statistical_cutoff_scaling n D d (by omega) hD]
        unfold mainStatisticalConstant
        ring
  have he2 : approximationConstant b d*A*(D:ℝ)/((n:ℝ)*((n:ℝ)^(-1/((d:ℝ)+6)))^(d+4))=
      approximationConstant b d*A*(D:ℝ)*(n:ℝ)^(-2/((d:ℝ)+6)) := by
    rw [←ha]
    ring
  rw [hc,he2]
  have hout := add_le_add hstat (le_refl (mainApproximationConstant b R A d*(D:ℝ)*(n:ℝ)^(-2/((d:ℝ)+6))))
  convert hout using 1
  unfold mainApproximationConstant
  ring

#print axioms cutoff_positive_and_le_one
#print axioms cutoff_log_bound
#print axioms statistical_cutoff_scaling
#print axioms main_bound_cutoff
end GeneralizationCheck
