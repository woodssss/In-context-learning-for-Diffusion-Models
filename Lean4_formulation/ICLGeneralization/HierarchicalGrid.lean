module

public import ICLGeneralization.FiniteBatchBound
public import ICLGeneralization.LemmaThreeComplete
public import ICLGeneralization.ParameterizedMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def levelTaskGap {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K : ℕ) (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω) (f : Ω → ℝ)
    (t : Fin K → Θ) : ℝ := hierarchicalPopulationLoss μ κTask κEpisode f-
      sampleAverage K (fun a => ∫ x, (∫ ω, f ω ∂κEpisode x) ∂κTask a) t

noncomputable def levelEpisodeGap {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J : ℕ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω) (f : Ω → ℝ)
    (p : (Fin K → Θ) × (Fin (K*J) → X)) : ℝ :=
  sampleAverage K (fun a => ∫ x, (∫ ω, f ω ∂κEpisode x) ∂κTask a) p.1-
    sampleAverage (K*J) (fun x => ∫ ω, f ω ∂κEpisode x) p.2

noncomputable def levelDiffusionGap {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (κEpisode : Kernel X Ω) (f : Ω → ℝ)
    (s : HierarchicalTrainingSample Θ X Ω K J N) : ℝ :=
  sampleAverage (K*J) (fun x => ∫ ω, f ω ∂κEpisode x) s.1.2-
    hierarchicalEmpiricalLoss K J N f s

theorem hierarchical_gap_decomposition {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω) (f : Ω → ℝ)
    (s : HierarchicalTrainingSample Θ X Ω K J N) :
    hierarchicalPopulationLoss μ κTask κEpisode f-hierarchicalEmpiricalLoss K J N f s =
      levelTaskGap K μ κTask κEpisode f s.1.1+levelEpisodeGap K J κTask κEpisode f s.1+
      levelDiffusionGap K J N κEpisode f s := by
  unfold levelTaskGap levelEpisodeGap levelDiffusionGap
  ring

theorem measurable_independent_sample_average {Y : Type*} [MeasurableSpace Y] (N : ℕ) (f : Y → ℝ) (hf : Measurable f) :
    Measurable (sampleAverage N f) := by
  unfold sampleAverage
  exact (Finset.measurable_sum _ (fun i _ => hf.comp (measurable_pi_apply i))).div_const _

theorem probability_product_integral_upper {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (κ : Kernel X Y) [IsMarkovKernel κ]
    (F : X × Y → ℝ) (hF : Measurable F) (M C : ℝ) (hb : ∀ p, |F p|≤M)
    (hi : ∀ x, (∫ y, F (x,y) ∂κ x)≤C) : (∫ p, F p ∂μ ⊗ₘ κ)≤C := by
  have hInt := (bounded_probability_integral (μ ⊗ₘ κ) F hF M hb).1
  rw [Measure.integral_compProd hInt]
  have hm : Measurable (fun x => ∫ y, F (x,y) ∂κ x) := hF.stronglyMeasurable.integral_kernel_prod_right' |>.measurable
  have hbb (x : X) : |∫ y, F (x,y) ∂κ x|≤M :=
    (bounded_probability_integral (κ x) _ (hF.comp (measurable_const.prodMk measurable_id)) M (fun y => hb (x,y))).2
  have h := integral_mono (bounded_probability_integral μ _ hm M hbb).1 (integrable_const C) hi
  simpa using h

theorem population_average_iid {Y : Type*} [MeasurableSpace Y] (N : ℕ) (hN : 0<N)
    (μ : Measure Y) (f : Y → ℝ) : populationAverage N (fun _ => μ) f = ∫ y, f y ∂μ := by
  unfold populationAverage
  simp [ne_of_gt hN]

theorem grid_diffusion_expectation {I Θ X Ω : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f : I → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (M H : ℝ) (hM : 0<M) (hH : 0<H)
    (hb : ∀ i ω, |f i ω|≤M) (hcard : Real.log (Fintype.card I:ℝ)≤H) :
    (∫ s, finiteMaximum (fun i => levelDiffusionGap K J N κEpisode (f i)) s
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤ 2*M*Real.sqrt H/Real.sqrt ((K*J)*N:ℝ) := by
  let h : I → X → ℝ := fun i x => ∫ ω, f i ω ∂κEpisode x
  have hm (i : I) : Measurable (h i) := kernel_average_measurable (fun (_ : Unit → ℝ) => f i) κEpisode (fun _ => 0) (hf i)
  have hB (i : I) (x : X) : |h i x|≤M := (bounded_probability_integral (κEpisode x) _ (hf i) M (hb i)).2
  have fm (i : I) : Measurable (levelDiffusionGap (Θ:=Θ) K J N κEpisode (f i)) :=
    ((measurable_independent_sample_average (K*J) (h i) (hm i)).comp measurable_fst.snd).sub
      (hierarchical_empirical_measurable K J N (f i) (hf i))
  have fB (i : I) (s : HierarchicalTrainingSample Θ X Ω K J N) : |levelDiffusionGap K J N κEpisode (f i) s|≤2*M :=
    (abs_sub _ _).trans ((add_le_add (independent_average_abs_bound _ (Nat.mul_pos hK hJ) (h i) M (hB i) s.1.2)
      (hierarchical_empirical_abs_bound K J N hK hJ hN (f i) M (hb i) s)).trans_eq (by ring))
  unfold hierarchicalTrainingLaw
  apply probability_product_integral_upper _ _ _ (finite_maximum_measurable _ fm) (2*M) _ (finite_maximum_abs_bound _ _ fB)
  intro p
  have he : (fun z => finiteMaximum (fun i => levelDiffusionGap K J N κEpisode (f i)) (p,z)) =
      finiteMaximum (fun i => sampleDeviation ((K*J)*N) (fun q => κEpisode (p.2 (parentIndex (K*J) N q))) (f i)) := by
    funext z
    unfold finiteMaximum
    congr 1
    funext i
    unfold levelDiffusionGap hierarchicalEmpiricalLoss sampleDeviation
    dsimp only
    rw [episode_population_average (K*J) N hN κEpisode (f i) p.2]
  rw [Kernel.comap_apply,he]
  simp only [diffusionBatchKernel,episodeBatchKernel,independent_batch_kernel_apply,Kernel.comap_apply]
  simpa only [Nat.cast_mul] using finite_batch_expectation_bound _ (Nat.mul_pos (Nat.mul_pos hK hJ) hN)
    (fun q => κEpisode (p.2 (parentIndex (K*J) N q))) f hf M H hM hH hb hcard

#print axioms hierarchical_gap_decomposition
#print axioms measurable_independent_sample_average
#print axioms probability_product_integral_upper
#print axioms population_average_iid
#print axioms grid_diffusion_expectation
end GeneralizationCheck
