module

public import ICLGeneralization.FiniteMaximum

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GeneralizationCheck

theorem population_average_abs_bound {Y : Type*} [MeasurableSpace Y] (N : ℕ) (hN : 0<N)
    (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (f : Y → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ y, |f y|≤M) : |populationAverage N μ f|≤M := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  unfold populationAverage
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using finite_sum_abs_bound N (fun i => ∫ y, f y ∂μ i) M
    (fun i => (bounded_probability_integral (μ i) f hf M hb).2)

theorem sample_deviation_measurable {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (μ : Fin N → Measure Y) (f : Y → ℝ) (hf : Measurable f) : Measurable (sampleDeviation N μ f) := by
  unfold sampleDeviation sampleAverage
  exact measurable_const.sub ((Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))).div_const _)

theorem sample_deviation_abs_bound {Y : Type*} [MeasurableSpace Y] (N : ℕ) (hN : 0<N)
    (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (f : Y → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ y, |f y|≤M) : ∀ x, |sampleDeviation N μ f x|≤2*M := by
  intro x
  exact (abs_sub _ _).trans ((add_le_add (population_average_abs_bound N hN μ f hf M hb)
    (independent_average_abs_bound N hN f M hb x)).trans_eq (by ring))

theorem finite_batch_expectation_bound {I Y : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Y]
    (N : ℕ) (hN : 0<N) (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
    (f : I → Y → ℝ) (hf : ∀ i, Measurable (f i)) (M H : ℝ) (hM : 0<M) (hH : 0<H)
    (hb : ∀ i y, |f i y|≤M) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ x, finiteMaximum (fun i => sampleDeviation N μ (f i)) x ∂Measure.pi μ) ≤
      2*M*Real.sqrt H/Real.sqrt (N:ℝ) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  let t := Real.sqrt (N:ℝ)*Real.sqrt H/M
  have ht : 0<t := by dsimp [t]; positivity
  have h := finite_maximum_exponential_bound (Measure.pi μ) (fun i => sampleDeviation N μ (f i))
    (fun i => sample_deviation_measurable N μ (f i) (hf i)) (2*M) (M^2/(N:ℝ)) t
    (fun i => sample_deviation_abs_bound N hN μ (f i) (hf i) M (hb i)) ht (fun i => by
      have hmg := (independent_average_subgaussian N hN μ (f i) (hf i) M hM.le (hb i)).mgf_le t
      exact hmg)
  have he : (M^2/(N:ℝ))*t^2/2 = H/2 := by
    dsimp [t]
    rw [div_pow,mul_pow,Real.sq_sqrt hn.le,Real.sq_sqrt hH.le]
    field_simp
  have htC : t*(2*M*Real.sqrt H/Real.sqrt (N:ℝ))=2*H := by
    dsimp [t]
    have hsp : Real.sqrt (N:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr hn)
    field_simp
    nlinarith [Real.sq_sqrt hH.le]
  rw [he] at h
  apply (mul_le_mul_iff_right₀ ht).mp
  rw [htC]
  linarith

#print axioms population_average_abs_bound
#print axioms sample_deviation_measurable
#print axioms sample_deviation_abs_bound
#print axioms finite_batch_expectation_bound
end GeneralizationCheck
