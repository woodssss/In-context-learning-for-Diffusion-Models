module

public import ICLGeneralization.HierarchicalGrid

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem probability_product_integral_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X Y) [IsMarkovKernel κ]
    (f : X → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ x, |f x|≤M) :
    (∫ p : X × Y, f p.1 ∂μ ⊗ₘ κ) = ∫ x, f x ∂μ := by
  have hm : Measurable (fun p : X × Y => f p.1) := hf.comp measurable_fst
  have hi := (bounded_probability_integral (μ ⊗ₘ κ) (fun p : X × Y => f p.1) hm M (fun p => hb p.1)).1
  rw [Measure.integral_compProd hi]
  simp

theorem grid_episode_expectation {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (_hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M H : ℝ) (hM : 0<M) (hH : 0<H)
    (hb : ∀ i ω, |f i ω|≤M) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ s, finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (f i)) s.1
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤ 2*M*Real.sqrt H/Real.sqrt (K*J:ℝ) := by
  let h : I → X → ℝ := fun i x => ∫ ω, f i ω ∂κEpisode x
  let g : I → Θ → ℝ := fun i t => ∫ x, h i x ∂κTask t
  have hm (i : I) : Measurable (h i) := kernel_average_measurable (fun (_ : Unit → ℝ) => f i) κEpisode (fun _ => 0) (hf i)
  have hB (i : I) (x : X) : |h i x|≤M := (bounded_probability_integral (κEpisode x) _ (hf i) M (hb i)).2
  have gm (i : I) : Measurable (g i) := kernel_average_measurable (fun (_ : Unit → ℝ) => h i) κTask (fun _ => 0) (hm i)
  have gB (i : I) (t : Θ) : |g i t|≤M := (bounded_probability_integral (κTask t) _ (hm i) M (hB i)).2
  have fm (i : I) : Measurable (levelEpisodeGap K J κTask κEpisode (f i)) :=
    ((measurable_independent_sample_average K (g i) (gm i)).comp measurable_fst).sub
      ((measurable_independent_sample_average (K*J) (h i) (hm i)).comp measurable_snd)
  have fB (i : I) (p : (Fin K → Θ) × (Fin (K*J) → X)) : |levelEpisodeGap K J κTask κEpisode (f i) p|≤2*M :=
    (abs_sub _ _).trans ((add_le_add (independent_average_abs_bound K hK (g i) M (gB i) p.1)
      (independent_average_abs_bound _ (Nat.mul_pos hK hJ) (h i) M (hB i) p.2)).trans_eq (by ring))
  have fmm := finite_maximum_measurable _ fm
  have fmB := finite_maximum_abs_bound _ (2*M) fB
  unfold hierarchicalTrainingLaw
  rw [probability_product_integral_fst _ _ _ fmm (2*M) fmB]
  apply probability_product_integral_upper _ _ _ fmm (2*M) _ fmB
  intro t
  have he : (fun x => finiteMaximum (fun i => levelEpisodeGap K J κTask κEpisode (f i)) (t,x)) =
      finiteMaximum (fun i => sampleDeviation (K*J) (fun q => κTask (t (parentIndex K J q))) (h i)) := by
    funext x
    unfold finiteMaximum
    congr 1
    funext i
    unfold levelEpisodeGap sampleDeviation
    dsimp only
    rw [episode_population_average K J hJ κTask (h i) t]
  rw [he]
  simp only [episodeBatchKernel,independent_batch_kernel_apply,Kernel.comap_apply]
  simpa only [Nat.cast_mul] using finite_batch_expectation_bound _ (Nat.mul_pos hK hJ)
    (fun q => κTask (t (parentIndex K J q))) h hm M H hM hH hB hcard

theorem grid_task_expectation {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (_hJ : 0<J) (_hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M H : ℝ) (hM : 0<M) (hH : 0<H)
    (hb : ∀ i ω, |f i ω|≤M) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ s, finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) s.1.1
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤ 2*M*Real.sqrt H/Real.sqrt (K:ℝ) := by
  let h : I → X → ℝ := fun i x => ∫ ω, f i ω ∂κEpisode x
  let g : I → Θ → ℝ := fun i t => ∫ x, h i x ∂κTask t
  have hm (i : I) : Measurable (h i) := kernel_average_measurable (fun (_ : Unit → ℝ) => f i) κEpisode (fun _ => 0) (hf i)
  have hB (i : I) (x : X) : |h i x|≤M := (bounded_probability_integral (κEpisode x) _ (hf i) M (hb i)).2
  have gm (i : I) : Measurable (g i) := kernel_average_measurable (fun (_ : Unit → ℝ) => h i) κTask (fun _ => 0) (hm i)
  have gB (i : I) (t : Θ) : |g i t|≤M := (bounded_probability_integral (κTask t) _ (hm i) M (hB i)).2
  have fm (i : I) : Measurable (levelTaskGap K μ κTask κEpisode (f i)) :=
    measurable_const.sub (measurable_independent_sample_average K (g i) (gm i))
  have fB (i : I) (t : Fin K → Θ) : |levelTaskGap K μ κTask κEpisode (f i) t|≤2*M :=
    (abs_sub _ _).trans ((add_le_add (bounded_probability_integral μ (g i) (gm i) M (gB i)).2
      (independent_average_abs_bound K hK (g i) M (gB i) t)).trans_eq (by ring))
  have fmm := finite_maximum_measurable _ fm
  have fmB := finite_maximum_abs_bound _ (2*M) fB
  unfold hierarchicalTrainingLaw
  have fpm : Measurable (fun p : (Fin K → Θ) × (Fin (K*J) → X) =>
      finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) p.1) := fmm.comp measurable_fst
  rw [probability_product_integral_fst _ _ (fun p : (Fin K → Θ) × (Fin (K*J) → X) =>
      finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) p.1) fpm (2*M) (fun p => fmB p.1)]
  rw [probability_product_integral_fst _ _ _ fmm (2*M) fmB]
  have he : finiteMaximum (fun i => levelTaskGap K μ κTask κEpisode (f i)) =
      finiteMaximum (fun i => sampleDeviation K (fun _ => μ) (g i)) := by
    funext t
    unfold finiteMaximum
    congr 1
    funext i
    unfold levelTaskGap sampleDeviation
    dsimp only
    rw [population_average_iid K hK μ (g i)]
    rfl
  rw [he]
  exact finite_batch_expectation_bound K hK (fun _ => μ) g gm M H hM hH gB hcard

#print axioms probability_product_integral_fst
#print axioms grid_episode_expectation
#print axioms grid_task_expectation
end GeneralizationCheck
