module

public import ICLGeneralization.GridExpectations

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem sample_average_distance {Y : Type*} (N : ℕ) (hN : 0<N)
    (f g : Y → ℝ) (η : ℝ) (he : ∀ y, |f y-g y|≤η) (x : Fin N → Y) :
    |sampleAverage N f x-sampleAverage N g x|≤η := by
  have hs : sampleAverage N f x-sampleAverage N g x = sampleAverage N (fun y => f y-g y) x := by
    unfold sampleAverage
    rw [Finset.sum_sub_distrib]
    ring
  rw [hs]
  exact independent_average_abs_bound N hN _ η he x

theorem hierarchical_population_abs_bound {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : Ω → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ ω, |f ω|≤M) : |hierarchicalPopulationLoss μ κTask κEpisode f|≤M := by
  let h := fun x => ∫ ω, f ω ∂κEpisode x
  have hm : Measurable h := kernel_average_measurable (fun (_ : Unit → ℝ) => f) κEpisode (fun _ => 0) hf
  have hB (x : X) : |h x|≤M := (bounded_probability_integral (κEpisode x) f hf M hb).2
  let g := fun t => ∫ x, h x ∂κTask t
  have gm : Measurable g := kernel_average_measurable (fun (_ : Unit → ℝ) => h) κTask (fun _ => 0) hm
  exact (bounded_probability_integral μ g gm M (fun t => (bounded_probability_integral (κTask t) h hm M hB).2)).2

theorem bounded_probability_integral_distance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M η : ℝ) (hb : ∀ ω, |f ω|≤M) (hb' : ∀ ω, |g ω|≤M) (he : ∀ ω, |f ω-g ω|≤η) :
    |(∫ ω, f ω ∂μ)-(∫ ω, g ω ∂μ)|≤η := by
  have hi := (bounded_probability_integral μ f hf M hb).1
  have hi' := (bounded_probability_integral μ g hg M hb').1
  have h := (bounded_probability_integral μ (fun ω => f ω-g ω) (hf.sub hg) η he).2
  rwa [integral_sub hi hi'] at h

theorem hierarchical_population_distance {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M η : ℝ) (hb : ∀ ω, |f ω|≤M) (hb' : ∀ ω, |g ω|≤M) (he : ∀ ω, |f ω-g ω|≤η) :
    |hierarchicalPopulationLoss μ κTask κEpisode f-hierarchicalPopulationLoss μ κTask κEpisode g|≤η := by
  have hfm := kernel_average_measurable (fun (_ : Unit → ℝ) => f) κEpisode (fun _ => 0) hf
  have hgm := kernel_average_measurable (fun (_ : Unit → ℝ) => g) κEpisode (fun _ => 0) hg
  have hhB (x : X) : |∫ ω, f ω ∂κEpisode x|≤M := (bounded_probability_integral (κEpisode x) f hf M hb).2
  have hhB' (x : X) : |∫ ω, g ω ∂κEpisode x|≤M := (bounded_probability_integral (κEpisode x) g hg M hb').2
  have hhe (x : X) : |(∫ ω, f ω ∂κEpisode x)-(∫ ω, g ω ∂κEpisode x)|≤η :=
    bounded_probability_integral_distance (κEpisode x) f g hf hg M η hb hb' he
  have gfm := kernel_average_measurable (fun (_ : Unit → ℝ) x => ∫ ω, f ω ∂κEpisode x) κTask (fun _ => 0) hfm
  have ggm := kernel_average_measurable (fun (_ : Unit → ℝ) x => ∫ ω, g ω ∂κEpisode x) κTask (fun _ => 0) hgm
  have ggB (t : Θ) : |∫ x, (∫ ω, f ω ∂κEpisode x) ∂κTask t|≤M := (bounded_probability_integral (κTask t) _ hfm M hhB).2
  have ggB' (t : Θ) : |∫ x, (∫ ω, g ω ∂κEpisode x) ∂κTask t|≤M := (bounded_probability_integral (κTask t) _ hgm M hhB').2
  have gge (t : Θ) : |(∫ x, (∫ ω, f ω ∂κEpisode x) ∂κTask t)-(∫ x, (∫ ω, g ω ∂κEpisode x) ∂κTask t)|≤η :=
    bounded_probability_integral_distance (κTask t) _ _ hfm hgm M η hhB hhB' hhe
  exact bounded_probability_integral_distance μ _ _ gfm ggm M η ggB ggB' gge

theorem hierarchical_grid_pointwise {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : Ω → ℝ) (hf : Measurable f) (c : I → Ω → ℝ) (hc : ∀ i, Measurable (c i))
    (M η : ℝ) (hb : ∀ ω, |f ω|≤M) (hbc : ∀ i ω, |c i ω|≤M)
    (hcover : ∃ i, ∀ ω, |f ω-c i ω|≤η) (s : HierarchicalTrainingSample Θ X Ω K J N) :
    hierarchicalPopulationLoss μ κTask κEpisode f-hierarchicalEmpiricalLoss K J N f s ≤
      finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (c i)) s.1.1+
      finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (c i)) s.1+
      finiteMaximum (fun i => levelDiffusionGap K J N κEpisode (c i)) s+2*η := by
  obtain ⟨i,he⟩ := hcover
  have hp := hierarchical_population_distance μ κTask κEpisode f (c i) hf (hc i) M η hb (hbc i) he
  have ha := sample_average_distance ((K*J)*N) (Nat.mul_pos (Nat.mul_pos hK hJ) hN) f (c i) η he s.2
  have ht := finite_maximum_le (fun i => levelTaskGap K μ κTask κEpisode (c i)) i s.1.1
  have hepi := finite_maximum_le (fun i => levelEpisodeGap K J κTask κEpisode (c i)) i s.1
  have hn := finite_maximum_le (fun i => levelDiffusionGap K J N κEpisode (c i)) i s
  have hd := hierarchical_gap_decomposition K J N μ κTask κEpisode (c i) s
  have hp' := abs_le.mp hp
  have ha' := abs_le.mp ha
  unfold hierarchicalEmpiricalLoss at hd ⊢
  linarith

#print axioms sample_average_distance
#print axioms hierarchical_population_abs_bound
#print axioms bounded_probability_integral_distance
#print axioms hierarchical_population_distance
#print axioms hierarchical_grid_pointwise
end GeneralizationCheck
