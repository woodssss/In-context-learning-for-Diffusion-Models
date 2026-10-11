module

public import ICLGeneralization.HierarchicalTraining
public import ICLGeneralization.BatchConcentration

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def hierarchicalSamplingFactor (K J N : ℕ) : ℝ :=
  1/Real.sqrt (K:ℝ)+1/Real.sqrt (K*J:ℝ)+1/Real.sqrt ((K*J)*N:ℝ)

theorem lemma_three_signed_expectation {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : Ω → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ ω, |f ω|≤M) :
    (∫ s, hierarchicalEmpiricalLoss K J N f s-hierarchicalPopulationLoss μ κTask κEpisode f
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) = 0 := by
  have hi := (bounded_probability_integral (hierarchicalTrainingLaw K J N μ κTask κEpisode) _
    (hierarchical_empirical_measurable K J N f hf) M
    (hierarchical_empirical_abs_bound K J N hK hJ hN f M hb)).1
  rw [integral_sub hi (integrable_const _),hierarchical_empirical_unbiased K J N hK hJ hN μ κTask κEpisode f hf M hb]
  simp

/- This is the manuscript's existing Lemma 3 inequality, with its exact
   epsilon-dependent right-hand side retained. -/
theorem lemma_three_original_bound {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : Ω → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ ω, |f ω|≤M)
    (ε : ℝ) (hε : 0<ε) (hε1 : ε<1) :
    (∫ s, hierarchicalEmpiricalLoss K J N f s-hierarchicalPopulationLoss μ κTask κEpisode f
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
    M*Real.sqrt (Real.log (1/ε)/2)*hierarchicalSamplingFactor K J N+6*ε*M := by
  rw [lemma_three_signed_expectation K J N hK hJ hN μ κTask κEpisode f hf M hb]
  have hlog : 0≤Real.log (1/ε) := Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  unfold hierarchicalSamplingFactor
  positivity

#print axioms lemma_three_signed_expectation
#print axioms lemma_three_original_bound
end GeneralizationCheck
