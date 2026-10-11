module

public import ICLGeneralization.KernelMoments
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_real_memLp (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ z, |f z| ≤ C) (p : ENNReal) : MemLp f p μ := by
  apply MemLp.of_bound hf.aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hC z)

theorem measurable_sample_average (n : ℕ) (f : Ω → ℝ) (hf : Measurable f) :
    Measurable (sampleAverage n f) := by
  unfold sampleAverage
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))

omit [MeasurableSpace Ω] in
theorem positive_sample_average (n : ℕ) (hn : 0 < n) (w : Ω → ℝ)
    (hw : ∀ z, 0 < w z) (ω : Fin n → Ω) : 0 < sampleAverage n w ω := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  unfold sampleAverage
  apply div_pos
  · exact Finset.sum_pos (fun i _ => hw (ω i)) Finset.univ_nonempty
  · exact_mod_cast hn

theorem positive_population_weight (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ)
    (hw : Integrable w μ) (hp : ∀ z, 0 < w z) : 0 < ∫ z, w z ∂μ := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (hp z).le) hw).2
  have he : Function.support w = Set.univ := by
    ext z
    simp [Function.mem_support, ne_of_gt (hp z)]
  simp [he]

noncomputable def empiricalWeightedMean (n : ℕ) (w x : Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  sampleAverage n (fun z => w z*x z) ω / sampleAverage n w ω

omit [MeasurableSpace Ω] in
theorem empirical_weighted_mean_bounds (n : ℕ) (hn : 0 < n) (w x : Ω → ℝ) (b : ℝ)
    (hw : ∀ z, 0 < w z) (hx : ∀ z, x z ∈ Set.Icc (-b) b) (ω : Fin n → Ω) :
    empiricalWeightedMean n w x ω ∈ Set.Icc (-b) b := by
  have hd := positive_sample_average n hn w hw ω
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlo : (-b)*sampleAverage n w ω ≤ sampleAverage n (fun z => w z*x z) ω := by
    unfold sampleAverage
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hn0
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (hx (ω i)).1 (hw (ω i)).le
    nlinarith [h]
  have hhi : sampleAverage n (fun z => w z*x z) ω ≤ b*sampleAverage n w ω := by
    unfold sampleAverage
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hn0
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hx (ω i)).2 (hw (ω i)).le
  exact ⟨(le_div_iff₀ hd).2 hlo, (div_le_iff₀ hd).2 hhi⟩

omit [MeasurableSpace Ω] in
theorem centered_sample_identity (n : ℕ) (w x : Ω → ℝ) (m : ℝ) (ω : Fin n → Ω) :
    sampleAverage n (fun z => w z*(x z-m)) ω =
      sampleAverage n (fun z => w z*x z) ω-m*sampleAverage n w ω := by
  simp only [sampleAverage, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

noncomputable def ratioError (n D : ℕ) (μ : Measure Ω) (w : Ω → ℝ) (x : Fin D → Ω → ℝ)
    (ω : Fin n → Ω) : ℝ :=
  ∑ j, (empiricalWeightedMean n w (x j) ω-weightedMean μ w (x j))^2

noncomputable def centeredNumeratorEnergy (n D : ℕ) (μ : Measure Ω) (w : Ω → ℝ)
    (x : Fin D → Ω → ℝ) (ω : Fin n → Ω) : ℝ :=
  ∑ j, (sampleAverage n (fun z => w z*(x j z-weightedMean μ w (x j))) ω)^2

theorem ratio_error_centered_identity (n D : ℕ) (hn : 0 < n) (μ : Measure Ω)
    (w : Ω → ℝ) (x : Fin D → Ω → ℝ) (hw : ∀ z, 0 < w z) (ω : Fin n → Ω) :
    ratioError n D μ w x ω = centeredNumeratorEnergy n D μ w x ω / (sampleAverage n w ω)^2 := by
  have hd := ne_of_gt (positive_sample_average n hn w hw ω)
  unfold ratioError centeredNumeratorEnergy
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [centered_sample_identity]
  unfold empiricalWeightedMean
  field_simp

theorem measurable_ratio_error (n D : ℕ) (μ : Measure Ω) (w : Ω → ℝ)
    (x : Fin D → Ω → ℝ) (hw : Measurable w) (hx : ∀ j, Measurable (x j)) :
    Measurable (ratioError n D μ w x) := by
  unfold ratioError
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_sample_average n _ (hw.mul (hx j))).div
    (measurable_sample_average n w hw) |>.sub_const _).pow_const 2

theorem fixed_query_ratio_error_bound (n D : ℕ) (hn : 0 < n)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ℝ) (x : Fin D → Ω → ℝ)
    (b : ℝ) (_hb : 0 ≤ b) (hw : Measurable w) (hwp : ∀ z, 0 < w z ∧ w z ≤ 1)
    (hx : ∀ j, Measurable (x j)) (hxb : ∀ j z, x j z ∈ Set.Icc (-b) b) :
    (∫ ω, ratioError n D μ w x ω ∂promptLaw n μ) ≤
      32*(D : ℝ)*b^2/(n : ℝ)*((∫ z, (w z)^2 ∂μ)/(∫ z, w z ∂μ)^2) := by
  classical
  have hwL2 := bounded_real_memLp μ w hw 1
    (fun z => by rw [abs_of_pos (hwp z).1]; exact (hwp z).2) 2
  have hwint := hwL2.integrable (by norm_num)
  have hwxL2 (j : Fin D) : MemLp (fun z => w z*x j z) 2 μ := by
    apply bounded_real_memLp μ _ (hw.mul (hx j)) b
    intro z
    change |w z*x j z| ≤ b
    rw [abs_mul, abs_of_pos (hwp z).1]
    exact (mul_le_mul (hwp z).2 (abs_le.mpr (hxb j z)) (abs_nonneg _) (by norm_num)).trans_eq
      (by ring)
  have hm := positive_population_weight μ w hwint (fun z => (hwp z).1)
  have hmean (j : Fin D) : weightedMean μ w (x j) ∈ Set.Icc (-b) b :=
    weighted_mean_bounds μ w (x j) b hwint ((hwxL2 j).integrable (by norm_num))
      (Filter.Eventually.of_forall (fun z => (hwp z).1.le))
      (Filter.Eventually.of_forall (hxb j)) hm
  have hcenterL2 (j : Fin D) :
      MemLp (fun z => w z*(x j z-weightedMean μ w (x j))) 2 μ := by
    have h := (hwxL2 j).sub (hwL2.mul_const (weightedMean μ w (x j)))
    convert h using 1
    funext z
    simp only [Pi.sub_apply, mul_sub]
  have henergyInt : Integrable (centeredNumeratorEnergy n D μ w x) (promptLaw n μ) := by
    apply integrable_finsetSum
    intro j _
    exact (sample_average_memLp n μ _ (hcenterL2 j)).integrable_sq
  have henergy := vector_centered_kernel_sample_second_moment n D hn μ w x b hwint
    (fun j => (hwxL2 j).integrable (by norm_num)) hm
    (Filter.Eventually.of_forall (fun z => (hwp z).1.le))
    (fun j => Filter.Eventually.of_forall (hxb j)) hwL2 hcenterL2
  have herrbound (ω : Fin n → Ω) : ratioError n D μ w x ω ≤ 4*(D : ℝ)*b^2 := by
    have h := vector_error_bound D (fun j => empiricalWeightedMean n w (x j) ω)
      (fun j => weightedMean μ w (x j)) b b
      (fun j => empirical_weighted_mean_bounds n hn w (x j) b (fun z => (hwp z).1) (hxb j) ω)
      hmean
    change (∑ j, _) ≤ _
    nlinarith
  have herrnonneg (ω : Fin n → Ω) : 0 ≤ ratioError n D μ w x ω :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have herrInt : Integrable (ratioError n D μ w x) (promptLaw n μ) :=
    (bounded_real_memLp (promptLaw n μ) _ (measurable_ratio_error n D μ w x hw hx)
      (4*(D : ℝ)*b^2) (fun ω => by rw [abs_of_nonneg (herrnonneg ω)]; exact herrbound ω) 1).integrable
      (le_refl _)
  let bad := {ω : Fin n → Ω | sampleAverage n w ω < (∫ z, w z ∂μ)/2}
  have hbad : MeasurableSet bad := measurableSet_lt (measurable_sample_average n w hw) measurable_const
  have hgoodPoint (ω : Fin n → Ω) (hω : ω ∈ badᶜ) :
      ratioError n D μ w x ω ≤ 4/(∫ z, w z ∂μ)^2*centeredNumeratorEnergy n D μ w x ω := by
    rw [ratio_error_centered_identity n D hn μ w x (fun z => (hwp z).1)]
    have h := good_event_division (centeredNumeratorEnergy n D μ w x ω) (∫ z, w z ∂μ)
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hm (sampleAverage n w ω)
      (le_of_not_gt hω)
    convert h using 1
    ring
  have hgood : (∫ ω in badᶜ, ratioError n D μ w x ω ∂promptLaw n μ) ≤
      4/(∫ z, w z ∂μ)^2*(∫ ω, centeredNumeratorEnergy n D μ w x ω ∂promptLaw n μ) := by
    rw [← integral_indicator hbad.compl, ← integral_const_mul]
    apply integral_mono_ae (herrInt.indicator hbad.compl) (henergyInt.const_mul _)
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases hω : ω ∈ badᶜ
      · rw [Set.indicator_of_mem hω]; exact hgoodPoint ω hω
      · rw [Set.indicator_of_notMem hω]
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hbadInt : (∫ ω in bad, ratioError n D μ w x ω ∂promptLaw n μ) ≤
      4*(D : ℝ)*b^2*(promptLaw n μ bad).toReal := by
    have h := integral_mono_ae (herrInt.restrict) (integrable_const (4*(D : ℝ)*b^2) :
      Integrable (fun _ : Fin n → Ω => 4*(D : ℝ)*b^2) ((promptLaw n μ).restrict bad))
      (Filter.Eventually.of_forall herrbound)
    simpa [integral_const, Measure.real, mul_comm] using h
  have hcheb := sample_denominator_chebyshev n hn μ w hwL2 hm
  have hv0 : 0 ≤ variance w μ := variance_nonneg w μ
  have hprob : (promptLaw n μ bad).toReal ≤ 4*variance w μ/((n : ℝ)*(∫ z, w z ∂μ)^2) := by
    have h := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hcheb
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    exact h
  have hvar : variance w μ ≤ ∫ z, (w z)^2 ∂μ := by
    rw [variance_eq_sub hwL2]
    simp only [Pi.pow_apply]
    exact sub_le_self _ (sq_nonneg _)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hbadBound := hbadInt.trans (mul_le_mul_of_nonneg_left hprob (by positivity))
  rw [← integral_add_compl hbad herrInt]
  have hg := hgood.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  have hbv := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hvar (by norm_num : (0 : ℝ) ≤ 4))
      (by positivity : 0 ≤ (n : ℝ)*(∫ z, w z ∂μ)^2))
    (show 0 ≤ 4*(D : ℝ)*b^2 by positivity)
  calc
    _ ≤ 4*(D : ℝ)*b^2*(4*variance w μ/((n : ℝ)*(∫ z, w z ∂μ)^2))+
        4/(∫ z, w z ∂μ)^2*(4*(D : ℝ)*b^2/(n : ℝ)*(∫ z, (w z)^2 ∂μ)) :=
      add_le_add hbadBound hg
    _ ≤ 4*(D : ℝ)*b^2*(4*(∫ z, (w z)^2 ∂μ)/((n : ℝ)*(∫ z, w z ∂μ)^2))+
        4/(∫ z, w z ∂μ)^2*(4*(D : ℝ)*b^2/(n : ℝ)*(∫ z, (w z)^2 ∂μ)) :=
      add_le_add hbv (le_refl _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

#print axioms bounded_real_memLp
#print axioms measurable_sample_average
#print axioms positive_sample_average
#print axioms positive_population_weight
#print axioms empirical_weighted_mean_bounds
#print axioms centered_sample_identity
#print axioms ratio_error_centered_identity
#print axioms measurable_ratio_error
#print axioms fixed_query_ratio_error_bound
end GeneralizationCheck
