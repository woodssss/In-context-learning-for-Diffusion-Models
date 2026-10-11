module

public import ICLGeneralization.GridMajorant

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def adaptiveHierarchyGap {P Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω)
    (f : P → Ω → ℝ) (learn : HierarchicalTrainingSample Θ X Ω K J N → P)
    (s : HierarchicalTrainingSample Θ X Ω K J N) : ℝ :=
  hierarchicalPopulationLoss μ κTask κEpisode (f (learn s))-hierarchicalEmpiricalLoss K J N (f (learn s)) s

theorem adaptive_gap_measurable {P Θ X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : P → Ω → ℝ)
    (hf : Measurable (fun p : P × Ω => f p.1 p.2))
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn) :
    Measurable (adaptiveHierarchyGap K J N μ κTask κEpisode f learn) := by
  have hm := joint_kernel_average_measurable f κEpisode hf
  have gm := joint_kernel_average_measurable (fun θ x => ∫ ω, f θ ω ∂κEpisode x) κTask hm
  have pm : Measurable (fun θ => hierarchicalPopulationLoss μ κTask κEpisode (f θ)) :=
    gm.stronglyMeasurable.integral_prod_right' |>.measurable
  have em : Measurable (fun s : HierarchicalTrainingSample Θ X Ω K J N => hierarchicalEmpiricalLoss K J N (f (learn s)) s) := by
    unfold hierarchicalEmpiricalLoss sampleAverage
    exact (Finset.measurable_sum _ (fun i _ => hf.comp (hl.prodMk ((measurable_pi_apply i).comp measurable_snd)))).div_const _
  exact (pm.comp hl).sub em

theorem adaptive_gap_integrable {P Θ X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : P → Ω → ℝ)
    (hf : Measurable (fun p : P × Ω => f p.1 p.2))
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn)
    (M : ℝ) (hb : ∀ θ ω, |f θ ω|≤M) :
    Integrable (adaptiveHierarchyGap K J N μ κTask κEpisode f learn) (hierarchicalTrainingLaw K J N μ κTask κEpisode) := by
  apply (bounded_probability_integral _ _ (adaptive_gap_measurable K J N μ κTask κEpisode f hf learn hl) (2*M) ?_).1
  intro s
  have hm : Measurable (f (learn s)) := hf.comp (measurable_const.prodMk measurable_id)
  exact (abs_sub _ _).trans ((add_le_add (hierarchical_population_abs_bound μ κTask κEpisode _ hm M (hb (learn s)))
    (hierarchical_empirical_abs_bound K J N hK hJ hN _ M (hb (learn s)) s)).trans_eq (by ring))

theorem adaptive_grid_bound {I P Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : P → Ω → ℝ)
    (hf : Measurable (fun p : P × Ω => f p.1 p.2))
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn)
    (c : I → P) (M H η : ℝ) (hM : 0<M) (hH : 0<H) (hb : ∀ θ ω, |f θ ω|≤M)
    (hcover : ∀ θ, ∃ i, ∀ ω, |f θ ω-f (c i) ω|≤η) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ s, adaptiveHierarchyGap K J N μ κTask κEpisode f learn s ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
      2*M*Real.sqrt H*hierarchicalSamplingFactor K J N+2*η := by
  have hm (θ : P) : Measurable (f θ) := hf.comp (measurable_const.prodMk measurable_id)
  have hi := adaptive_gap_integrable K J N hK hJ hN μ κTask κEpisode f hf learn hl M hb
  have hgrid := grid_majorant_controls K J N hK hJ hN μ κTask κEpisode (fun i => f (c i)) (fun i => hm (c i)) M (fun i => hb (c i))
  have hgi := (bounded_probability_integral (hierarchicalTrainingLaw K J N μ κTask κEpisode)
    (gridMajorant K J N μ κTask κEpisode (fun i => f (c i))) hgrid.1 (6*M) hgrid.2).1
  have hpoint (s) : adaptiveHierarchyGap K J N μ κTask κEpisode f learn s ≤
      gridMajorant K J N μ κTask κEpisode (fun i => f (c i)) s+2*η :=
    hierarchical_grid_pointwise K J N hK hJ hN μ κTask κEpisode (f (learn s)) (hm (learn s))
      (fun i => f (c i)) (fun i => hm (c i)) M η (hb (learn s)) (fun i => hb (c i)) (hcover (learn s)) s
  have hsumI : Integrable (fun s => gridMajorant K J N μ κTask κEpisode (fun i => f (c i)) s+2*η)
      (hierarchicalTrainingLaw K J N μ κTask κEpisode) := hgi.add (integrable_const _)
  have h := integral_mono hi hsumI hpoint
  rw [integral_add hgi (integrable_const _)] at h
  simp only [integral_const,probReal_univ,one_smul] at h
  exact h.trans (add_le_add (grid_majorant_expectation K J N hK hJ hN μ κTask κEpisode
    (fun i => f (c i)) (fun i => hm (c i)) M H hM hH (fun i => hb (c i)) hcard) (le_refl (2*η)))

#print axioms adaptive_gap_measurable
#print axioms adaptive_gap_integrable
#print axioms adaptive_grid_bound
end GeneralizationCheck
