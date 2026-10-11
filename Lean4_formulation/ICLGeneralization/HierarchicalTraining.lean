module

public import ICLGeneralization.IndependentBatch
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

def parentIndex (K J : ℕ) (i : Fin (K*J)) : Fin K := (finProdFinEquiv.symm i).1

noncomputable def episodeBatchKernel {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K J : ℕ) (κ : Kernel Θ X) : Kernel (Fin K → Θ) (Fin (K*J) → X) :=
  independentBatchKernel (K*J) (fun i => κ.comap (fun t => t (parentIndex K J i)) (measurable_pi_apply _))

noncomputable def diffusionBatchKernel {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (κ : Kernel X Ω) : Kernel (Fin (K*J) → X) (Fin ((K*J)*N) → Ω) :=
  episodeBatchKernel (K*J) N κ

instance episode_batch_markov {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K J : ℕ) (κ : Kernel Θ X) [IsMarkovKernel κ] : IsMarkovKernel (episodeBatchKernel K J κ) := by
  unfold episodeBatchKernel
  infer_instance

instance diffusion_batch_markov {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (κ : Kernel X Ω) [IsMarkovKernel κ] : IsMarkovKernel (diffusionBatchKernel K J N κ) := by
  unfold diffusionBatchKernel
  infer_instance

abbrev HierarchicalTrainingSample (Θ X Ω : Type*) (K J N : ℕ) :=
  ((Fin K → Θ) × (Fin (K*J) → X)) × (Fin ((K*J)*N) → Ω)

noncomputable def hierarchicalTrainingLaw {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω) :
    Measure (HierarchicalTrainingSample Θ X Ω K J N) :=
  ((promptLaw K μ) ⊗ₘ (episodeBatchKernel K J κTask)) ⊗ₘ
    ((diffusionBatchKernel K J N κEpisode).comap Prod.snd measurable_snd)

instance hierarchical_training_probability {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (μ : Measure Θ) [IsProbabilityMeasure μ]
    (κTask : Kernel Θ X) [IsMarkovKernel κTask] (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] :
    IsProbabilityMeasure (hierarchicalTrainingLaw K J N μ κTask κEpisode) := by
  unfold hierarchicalTrainingLaw
  infer_instance

noncomputable def hierarchicalEmpiricalLoss {Θ X Ω : Type*} (K J N : ℕ) (f : Ω → ℝ)
    (s : HierarchicalTrainingSample Θ X Ω K J N) : ℝ := sampleAverage ((K*J)*N) f s.2

noncomputable def hierarchicalPopulationLoss {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Θ) (κTask : Kernel Θ X) (κEpisode : Kernel X Ω) (f : Ω → ℝ) : ℝ :=
  ∫ t, (∫ x, (∫ ω, f ω ∂κEpisode x) ∂κTask t) ∂μ

theorem parent_index_sum (K J : ℕ) (g : Fin K → ℝ) :
    (∑ i : Fin (K*J),g (parentIndex K J i)) = (J:ℝ)*(∑ k,g k) := by
  classical
  have h := Equiv.sum_comp finProdFinEquiv (fun i : Fin (K*J) => g (parentIndex K J i))
  rw [←h]
  simp [parentIndex,Fintype.sum_prod_type,Finset.mul_sum]

theorem episode_population_average {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K J : ℕ) (hJ : 0<J) (κ : Kernel Θ X) (f : X → ℝ) (t : Fin K → Θ) :
    populationAverage (K*J) (fun i => κ (t (parentIndex K J i))) f =
      sampleAverage K (fun a => ∫ x, f x ∂κ a) t := by
  unfold populationAverage sampleAverage
  have hs := parent_index_sum K J (fun k => ∫ y, f y ∂κ (t k))
  rw [hs]
  simp only [Nat.cast_mul]
  have hj : (J:ℝ)≠0 := by exact_mod_cast ne_of_gt hJ
  field_simp

theorem hierarchical_empirical_measurable {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (f : Ω → ℝ) (hf : Measurable f) : Measurable (hierarchicalEmpiricalLoss (Θ:=Θ) (X:=X) K J N f) := by
  unfold hierarchicalEmpiricalLoss sampleAverage
  exact (Finset.measurable_sum _ (fun i _ => hf.comp ((measurable_pi_apply i).comp measurable_snd))).div_const _

theorem hierarchical_empirical_abs_bound {Θ X Ω : Type*}
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N) (f : Ω → ℝ) (M : ℝ) (hb : ∀ ω, |f ω|≤M)
    (s : HierarchicalTrainingSample Θ X Ω K J N) : |hierarchicalEmpiricalLoss K J N f s|≤M :=
  independent_average_abs_bound _ (Nat.mul_pos (Nat.mul_pos hK hJ) hN) f M hb s.2

theorem hierarchical_empirical_unbiased {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (f : Ω → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ ω, |f ω|≤M) :
    (∫ s, hierarchicalEmpiricalLoss K J N f s ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) =
      hierarchicalPopulationLoss μ κTask κEpisode f := by
  let h : X → ℝ := fun x => ∫ ω, f ω ∂κEpisode x
  let g : Θ → ℝ := fun t => ∫ x, h x ∂κTask t
  have hm : Measurable h := kernel_average_measurable (fun (_ : Unit → ℝ) => f) κEpisode (fun _ => 0) hf
  have hB (x : X) : |h x|≤M := (bounded_probability_integral (κEpisode x) f hf M hb).2
  have gm : Measurable g := kernel_average_measurable (fun (_ : Unit → ℝ) => h) κTask (fun _ => 0) hm
  have gB (t : Θ) : |g t|≤M := (bounded_probability_integral (κTask t) h hm M hB).2
  have hi := (bounded_probability_integral (hierarchicalTrainingLaw K J N μ κTask κEpisode) _
    (hierarchical_empirical_measurable K J N f hf) M
    (hierarchical_empirical_abs_bound K J N hK hJ hN f M hb)).1
  rw [hierarchicalTrainingLaw,Measure.integral_compProd hi]
  simp only [Kernel.comap_apply]
  have he (p : (Fin K → Θ) × (Fin (K*J) → X)) :
      (∫ z, hierarchicalEmpiricalLoss K J N f (p,z)
        ∂diffusionBatchKernel K J N κEpisode p.2) = sampleAverage (K*J) h p.2 := by
    simp only [hierarchicalEmpiricalLoss,Kernel.comap_apply,diffusionBatchKernel,episodeBatchKernel,
      independent_batch_kernel_apply,Kernel.comap_apply]
    rw [independent_average_integral _ _ f (fun i => (bounded_probability_integral _ f hf M hb).1),
      episode_population_average (K*J) N hN]
  simp_rw [he]
  have hem : Measurable (fun p : (Fin K → Θ) × (Fin (K*J) → X) => sampleAverage (K*J) h p.2) := by
    unfold sampleAverage
    exact (Finset.measurable_sum _ (fun i _ => hm.comp ((measurable_pi_apply i).comp measurable_snd))).div_const _
  have hi2 := (bounded_probability_integral ((promptLaw K μ) ⊗ₘ (episodeBatchKernel K J κTask))
    (fun p => sampleAverage (K*J) h p.2)
    hem M
    (fun p => independent_average_abs_bound _ (Nat.mul_pos hK hJ) h M hB p.2)).1
  rw [Measure.integral_compProd hi2]
  have he2 (t : Fin K → Θ) : (∫ x, sampleAverage (K*J) h x ∂episodeBatchKernel K J κTask t) = sampleAverage K g t := by
    simp only [episodeBatchKernel,independent_batch_kernel_apply,Kernel.comap_apply]
    rw [independent_average_integral _ _ h (fun i => (bounded_probability_integral _ h hm M hB).1),
      episode_population_average K J hJ]
  simp_rw [he2]
  exact sample_average_integral K hK μ g (bounded_probability_integral μ g gm M gB).1

#print axioms parent_index_sum
#print axioms episode_population_average
#print axioms hierarchical_empirical_measurable
#print axioms hierarchical_empirical_abs_bound
#print axioms hierarchical_empirical_unbiased
end GeneralizationCheck
