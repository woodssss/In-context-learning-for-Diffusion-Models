module

public import ICLGeneralization.StatisticalFinal

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem adaptive_population_measurable {P Θ X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : P → Ω → ℝ)
    (hf : Measurable (fun p : P × Ω => f p.1 p.2))
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn) :
    Measurable (fun z => hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))) := by
  have hm := joint_kernel_average_measurable f κEpisode hf
  have gm := joint_kernel_average_measurable (fun θ x => ∫ ω, f θ ω ∂κEpisode x) κTask hm
  exact (gm.stronglyMeasurable.integral_prod_right' |>.measurable).comp hl

theorem erm_expected_excess {P Θ X Ω : Type*}
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
      hierarchicalPopulationLoss μ κTask κEpisode (f candidate)-oracle := by
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
  have hpoint (z) : hierarchicalPopulationLoss μ κTask κEpisode (f (learn z))-oracle≤
      adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+hierarchicalEmpiricalLoss K J N (f candidate) z-oracle := by
    have h := herm z candidate
    unfold adaptiveHierarchyGap
    linarith
  have hri : Integrable (fun z => adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+
      hierarchicalEmpiricalLoss K J N (f candidate) z-oracle) law := (hgi.add hei).sub (integrable_const _)
  have hsumI : Integrable (fun z => adaptiveHierarchyGap K J N μ κTask κEpisode f learn z+
      hierarchicalEmpiricalLoss K J N (f candidate) z) law := hgi.add hei
  have h := integral_mono (hpi.sub (integrable_const oracle)) hri hpoint
  rw [integral_sub hsumI (integrable_const _),integral_add hgi hei] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  rw [hierarchical_empirical_unbiased K J N hK hJ hN μ κTask κEpisode _ (hfm candidate) M (hb candidate)] at h
  exact h

#print axioms adaptive_population_measurable
#print axioms erm_expected_excess
end GeneralizationCheck
