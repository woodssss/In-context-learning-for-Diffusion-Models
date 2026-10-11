module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def promptLaw (n : ℕ) (μ : Measure Ω) : Measure (Fin n → Ω) :=
  Measure.pi (fun _ => μ)

instance (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (promptLaw n μ) := by
  unfold promptLaw
  infer_instance

noncomputable def sampleAverage (n : ℕ) (f : Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  (∑ i, f (ω i)) / (n : ℝ)

theorem sample_average_memLp (n : ℕ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    MemLp (sampleAverage n f) 2 (promptLaw n μ) := by
  have h := memLp_finsetSum Finset.univ (fun i _ =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))
  unfold sampleAverage promptLaw
  simpa only [Function.comp_apply, div_eq_mul_inv] using h.mul_const (n : ℝ)⁻¹

theorem sample_average_integral (n : ℕ) (hn : 0 < n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Integrable f μ) :
    ∫ ω, sampleAverage n f ω ∂promptLaw n μ = ∫ x, f x ∂μ := by
  have hev (i : Fin n) :
      ∫ ω, f (ω i) ∂promptLaw n μ = ∫ x, f x ∂μ := by
    have hm := measurePreserving_eval (fun _ : Fin n => μ) i
    have hfmap : AEStronglyMeasurable f
        (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin n => μ))) := by
      rw [hm.map_eq]
      exact hf.aestronglyMeasurable
    have h := integral_map hm.measurable.aemeasurable hfmap
    rw [hm.map_eq] at h
    exact h.symm
  simp only [sampleAverage]
  rw [integral_div, integral_finsetSum]
  · simp_rw [hev]
    simp [ne_of_gt hn]
  · intro i _
    exact (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hf

theorem sample_average_variance (n : ℕ) (hn : 0 < n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    variance (sampleAverage n f) (promptLaw n μ) = variance f μ / (n : ℝ) := by
  unfold sampleAverage promptLaw
  simp only [div_eq_mul_inv]
  rw [variance_mul_const]
  have h := variance_sum_pi (fun _ : Fin n => hf)
  have hfun : (∑ i : Fin n, fun ω : Fin n → Ω => f (ω i)) =
      (fun ω => ∑ i, f (ω i)) := by
    funext ω
    simp
  rw [hfun] at h
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp

theorem centered_sample_average_second_moment (n : ℕ) (hn : 0 < n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ)
    (hzero : ∫ x, f x ∂μ = 0) :
    ∫ ω, (sampleAverage n f ω)^2 ∂promptLaw n μ =
      (∫ x, (f x)^2 ∂μ) / (n : ℝ) := by
  have hm := sample_average_integral n hn μ f (hf.integrable (by norm_num))
  rw [hzero] at hm
  rw [← variance_of_integral_eq_zero (sample_average_memLp n μ f hf).aemeasurable hm,
    sample_average_variance n hn μ f hf, variance_of_integral_eq_zero hf.aemeasurable hzero]

theorem sample_denominator_chebyshev (n : ℕ) (hn : 0 < n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : MemLp w 2 μ)
    (hm : 0 < ∫ x, w x ∂μ) :
    promptLaw n μ {ω | sampleAverage n w ω < (∫ x, w x ∂μ)/2} ≤
      ENNReal.ofReal (4 * variance w μ / ((n : ℝ) * (∫ x, w x ∂μ)^2)) := by
  let m := ∫ x, w x ∂μ
  have hav := sample_average_memLp n μ w hw
  have havmean := sample_average_integral n hn μ w (hw.integrable (by norm_num))
  have hset : {ω | sampleAverage n w ω < m/2} ⊆
      {ω | m/2 ≤ |sampleAverage n w ω - ∫ η, sampleAverage n w η ∂promptLaw n μ|} := by
    intro ω hω
    rw [havmean]
    change m/2 ≤ |sampleAverage n w ω-m|
    have hneg : sampleAverage n w ω - m < 0 := by dsimp [m] at *; linarith
    rw [abs_of_neg hneg]
    dsimp [m] at *
    linarith
  have hc := meas_ge_le_variance_div_sq hav (show 0 < m/2 by dsimp [m]; positivity)
  have he : variance (sampleAverage n w) (promptLaw n μ) / (m/2)^2 =
      4 * variance w μ / ((n : ℝ) * m^2) := by
    rw [sample_average_variance n hn μ w hw]
    have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have hmp : m ≠ 0 := ne_of_gt hm
    field_simp
    ring
  rw [he] at hc
  exact le_trans (measure_mono hset) hc

theorem sample_denominator_second_moment_bound (n : ℕ) (hn : 0 < n) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (w : Ω → ℝ) (hw : MemLp w 2 μ)
    (hm : 0 < ∫ x, w x ∂μ) :
    promptLaw n μ {ω | sampleAverage n w ω < (∫ x, w x ∂μ)/2} ≤
      ENNReal.ofReal (4/(n : ℝ)*
        ((∫ x, (w x)^2 ∂μ)/(∫ x, w x ∂μ)^2-1)) := by
  have h := sample_denominator_chebyshev n hn μ w hw hm
  have he : 4*variance w μ/((n : ℝ)*(∫ x, w x ∂μ)^2) =
      4/(n : ℝ)*((∫ x, (w x)^2 ∂μ)/(∫ x, w x ∂μ)^2-1) := by
    rw [variance_eq_sub hw]
    simp only [Pi.pow_apply]
    have hnp : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
    have hmp := ne_of_gt hm
    field_simp
  rw [he] at h
  exact h

#print axioms sample_average_memLp
#print axioms sample_average_integral
#print axioms sample_average_variance
#print axioms centered_sample_average_second_moment
#print axioms sample_denominator_chebyshev
#print axioms sample_denominator_second_moment_bound
end GeneralizationCheck
