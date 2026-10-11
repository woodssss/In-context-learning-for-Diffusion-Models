module

public import ICLGeneralization.PropositionOneComplete
public import Mathlib.Probability.Distributions.Uniform

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

abbrev LegalTime (δ : ℝ) := Set.Icc δ (1 : ℝ)

noncomputable def uniformTimeLaw (δ : ℝ) : Measure (LegalTime δ) :=
  (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc δ 1)).comap Subtype.val

instance (δ : ℝ) [Fact (δ < 1)] : IsProbabilityMeasure (uniformTimeLaw δ) := by
  have hδ : δ < 1 := Fact.out
  let : IsProbabilityMeasure (ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc δ 1)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith)))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).isProbabilityMeasure_comap
    (by simpa only [Subtype.range_coe] using
      (ProbabilityTheory.ae_cond_mem (μ := (volume : Measure ℝ)) measurableSet_Icc))

theorem uniform_time_law_map (δ : ℝ) :
    (uniformTimeLaw δ).map (Subtype.val : LegalTime δ → ℝ) =
      ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc δ 1) := by
  unfold uniformTimeLaw
  rw [map_comap_subtype_coe measurableSet_Icc]
  exact Measure.restrict_eq_self_of_ae_mem
    (ProbabilityTheory.ae_cond_mem (μ := (volume : Measure ℝ)) measurableSet_Icc)

theorem proposition_one_uniform_time {Θ : Type*} [MeasurableSpace Θ]
    (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D) (S : Set (KernelSpace D)) (hS : IsCompact S)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (b R A s0 δ : ℝ) (hδ : δ < 1) (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (a s : LegalTime δ → ℝ) (ha : Measurable a) (hs : Measurable s)
    (haRange : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hsRange : ∀ t, s0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∀ j, InScalarTransformerClass
      (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (approximationWeightBudget n D b R s0)) ∧
    candidatePopulationRisk n D (μTask.prod (uniformTimeLaw δ)) (ρ.comap Prod.fst measurable_fst)
      b R (noiseRadius D s0) s0 (a ∘ Prod.snd) (s ∘ Prod.snd)-
    oraclePopulationRisk D (μTask.prod (uniformTimeLaw δ)) (ρ.comap Prod.fst measurable_fst)
      (a ∘ Prod.snd) (s ∘ Prod.snd) ≤
    approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  let : Fact (δ < 1) := ⟨hδ⟩
  exact proposition_one_independent_task_time n D d hn hD S hS μTask (uniformTimeLaw δ)
    ρ b R A s0 hb hR hA hs0 hs01 a s ha hs haRange hsRange hbox hcover

#print axioms uniform_time_law_map
#print axioms proposition_one_uniform_time
end GeneralizationCheck
