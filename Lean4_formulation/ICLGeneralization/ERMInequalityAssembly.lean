module

public import ICLGeneralization.MainTheorem

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem erm_expected_excess_three_terms {P Θ X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : P → Ω → ℝ)
    (hf : Measurable (fun p : P × Ω => f p.1 p.2)) (M : ℝ) (hb : ∀ p ω, |f p ω|≤M)
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn)
    (herm : ∀ z p, hierarchicalEmpiricalLoss K J N (f (learn z)) z≤hierarchicalEmpiricalLoss K J N (f p) z)
    (candidate : P) (oracle : ℝ) :
    (∫ z, hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))-oracle
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
      (∫ z, adaptiveHierarchyGap K J N μ κTask κEpisode f learn z
        ∂hierarchicalTrainingLaw K J N μ κTask κEpisode)+
      (∫ z, hierarchicalEmpiricalLoss K J N (f candidate) z-
        hierarchicalPopulationLoss μ κTask κEpisode (f candidate)
        ∂hierarchicalTrainingLaw K J N μ κTask κEpisode)+
      (hierarchicalPopulationLoss μ κTask κEpisode (f candidate)-oracle) := by
  let law := hierarchicalTrainingLaw K J N μ κTask κEpisode
  have hfm (p : P) : Measurable (f p) := hf.comp (measurable_const.prodMk measurable_id)
  have hpB (z) : |hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))|≤M :=
    hierarchical_population_abs_bound μ κTask κEpisode _ (hfm (learn z)) M (hb (learn z))
  have hpi : Integrable (fun z => hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))) law :=
    (bounded_probability_integral law _ (adaptive_population_measurable K J N μ κTask κEpisode f hf learn hl) M hpB).1
  have hgi := adaptive_gap_integrable K J N hK hJ hN μ κTask κEpisode f hf learn hl M hb
  have hei : Integrable (hierarchicalEmpiricalLoss (Θ:=Θ) (X:=X) K J N (f candidate)) law :=
    (bounded_probability_integral law _ (hierarchical_empirical_measurable K J N _ (hfm candidate)) M
      (hierarchical_empirical_abs_bound K J N hK hJ hN _ M (hb candidate))).1
  let gII := fun z : HierarchicalTrainingSample Θ X Ω K J N => hierarchicalEmpiricalLoss K J N (f candidate) z-
    hierarchicalPopulationLoss μ κTask κEpisode (f candidate)
  have hII : Integrable gII law := hei.sub (integrable_const _)
  have hsum : Integrable (fun z => adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+gII z) law := hgi.add hII
  have hpoint (z) : hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))-oracle ≤
      adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+gII z+
      (hierarchicalPopulationLoss μ κTask κEpisode (f candidate)-oracle) :=
    erm_decomposition _ _ _ _ _ (herm z candidate)
  have hright : Integrable (fun z => adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+gII z+
      (hierarchicalPopulationLoss μ κTask κEpisode (f candidate)-oracle)) law := hsum.add (integrable_const _)
  have h := integral_mono (hpi.sub (integrable_const oracle))
    hright hpoint
  rw [integral_add hsum (integrable_const _),integral_add hgi hII] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  dsimp only [gII,Pi.sub_apply] at h
  exact h

#print axioms erm_expected_excess_three_terms
end GeneralizationCheck
