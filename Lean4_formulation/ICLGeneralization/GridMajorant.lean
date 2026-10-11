module

public import ICLGeneralization.GridStability

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def gridMajorant {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω)
    (f : I → Ω → ℝ) (s : HierarchicalTrainingSample Θ X Ω K J N) : ℝ :=
  finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) s.1.1+
    finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (f i)) s.1+
    finiteMaximum (fun i => levelDiffusionGap K J N κEpisode (f i)) s

theorem grid_level_controls {I Θ X Ω : Type*} [Fintype I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M : ℝ) (hb : ∀ i ω, |f i ω|≤M) :
    (∀ i, Measurable (levelTaskGap K μ κTask κEpisode (f i))) ∧
    (∀ i t, |levelTaskGap K μ κTask κEpisode (f i) t|≤2*M) ∧
    (∀ i, Measurable (levelEpisodeGap K J κTask κEpisode (f i))) ∧
    (∀ i p, |levelEpisodeGap K J κTask κEpisode (f i) p|≤2*M) ∧
    (∀ i, Measurable (levelDiffusionGap (Θ:=Θ) K J N κEpisode (f i))) ∧
    (∀ i s, |levelDiffusionGap (Θ:=Θ) K J N κEpisode (f i) s|≤2*M) := by
  let h : I → X → ℝ := fun i x => ∫ ω, f i ω ∂κEpisode x
  let g : I → Θ → ℝ := fun i t => ∫ x, h i x ∂κTask t
  have hm (i : I) : Measurable (h i) := kernel_average_measurable (fun (_ : Unit → ℝ) => f i) κEpisode (fun _ => 0) (hf i)
  have hB (i : I) (x : X) : |h i x|≤M := (bounded_probability_integral (κEpisode x) _ (hf i) M (hb i)).2
  have gm (i : I) : Measurable (g i) := kernel_average_measurable (fun (_ : Unit → ℝ) => h i) κTask (fun _ => 0) (hm i)
  have gB (i : I) (t : Θ) : |g i t|≤M := (bounded_probability_integral (κTask t) _ (hm i) M (hB i)).2
  refine ⟨fun i => measurable_const.sub (measurable_independent_sample_average K (g i) (gm i)),?_,
    fun i => ((measurable_independent_sample_average K (g i) (gm i)).comp measurable_fst).sub
      ((measurable_independent_sample_average (K*J) (h i) (hm i)).comp measurable_snd),?_,
    fun i => ((measurable_independent_sample_average (K*J) (h i) (hm i)).comp measurable_fst.snd).sub
      (hierarchical_empirical_measurable K J N (f i) (hf i)),?_⟩
  · intro i t
    exact (abs_sub _ _).trans ((add_le_add (hierarchical_population_abs_bound μ κTask κEpisode (f i) (hf i) M (hb i))
      (independent_average_abs_bound K hK (g i) M (gB i) t)).trans_eq (by ring))
  · intro i p
    exact (abs_sub _ _).trans ((add_le_add (independent_average_abs_bound K hK (g i) M (gB i) p.1)
      (independent_average_abs_bound _ (Nat.mul_pos hK hJ) (h i) M (hB i) p.2)).trans_eq (by ring))
  · intro i s
    exact (abs_sub _ _).trans ((add_le_add (independent_average_abs_bound _ (Nat.mul_pos hK hJ) (h i) M (hB i) s.1.2)
      (hierarchical_empirical_abs_bound K J N hK hJ hN (f i) M (hb i) s)).trans_eq (by ring))

theorem grid_majorant_controls {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M : ℝ) (hb : ∀ i ω, |f i ω|≤M) :
    Measurable (gridMajorant K J N μ κTask κEpisode f) ∧
      ∀ s, |gridMajorant K J N μ κTask κEpisode f s|≤6*M := by
  obtain ⟨tm,tB,em,eB,nm,nB⟩ := grid_level_controls K J N hK hJ hN μ κTask κEpisode f hf M hb
  constructor
  · exact (((finite_maximum_measurable _ tm).comp measurable_fst.fst).add
      ((finite_maximum_measurable _ em).comp measurable_fst)).add (finite_maximum_measurable _ nm)
  · intro s
    have ht := finite_maximum_abs_bound _ (2*M) tB s.1.1
    have he := finite_maximum_abs_bound _ (2*M) eB s.1
    have hn := finite_maximum_abs_bound _ (2*M) nB s
    exact (abs_add_le _ _).trans (((add_le_add ((abs_add_le _ _).trans (add_le_add ht he)) hn)).trans_eq (by ring))

theorem grid_majorant_expectation {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M H : ℝ) (hM : 0<M) (hH : 0<H)
    (hb : ∀ i ω, |f i ω|≤M) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ s, gridMajorant K J N μ κTask κEpisode f s ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
      2*M*Real.sqrt H*hierarchicalSamplingFactor K J N := by
  obtain ⟨tm,tB,em,eB,nm,nB⟩ := grid_level_controls K J N hK hJ hN μ κTask κEpisode f hf M hb
  let law := hierarchicalTrainingLaw K J N μ κTask κEpisode
  have hti := (bounded_probability_integral law
    (fun s : HierarchicalTrainingSample Θ X Ω K J N => finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) s.1.1) ((finite_maximum_measurable _ tm).comp measurable_fst.fst)
    (2*M) (fun s => finite_maximum_abs_bound _ (2*M) tB s.1.1)).1
  have hei := (bounded_probability_integral law
    (fun s : HierarchicalTrainingSample Θ X Ω K J N => finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (f i)) s.1) ((finite_maximum_measurable _ em).comp measurable_fst)
    (2*M) (fun s => finite_maximum_abs_bound _ (2*M) eB s.1)).1
  have hni := (bounded_probability_integral law
    (finiteMaximum (fun i => levelDiffusionGap K J N κEpisode (f i))) (finite_maximum_measurable _ nm)
    (2*M) (finite_maximum_abs_bound _ (2*M) nB)).1
  have ht := grid_task_expectation K J N hK hJ hN μ κTask κEpisode f hf M H hM hH hb hcard
  have he := grid_episode_expectation K J N hK hJ hN μ κTask κEpisode f hf M H hM hH hb hcard
  have hn := grid_diffusion_expectation K J N hK hJ hN μ κTask κEpisode f hf M H hM hH hb hcard
  have hi12 : Integrable (fun s : HierarchicalTrainingSample Θ X Ω K J N =>
      finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) s.1.1+
      finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (f i)) s.1) law := hti.add hei
  have hadd := integral_add hi12 hni
  have hadd12 := integral_add hti hei
  unfold gridMajorant
  rw [hadd,hadd12]
  apply (add_le_add (add_le_add ht he) hn).trans_eq
  unfold hierarchicalSamplingFactor
  ring

#print axioms grid_level_controls
#print axioms grid_majorant_controls
#print axioms grid_majorant_expectation
end GeneralizationCheck
