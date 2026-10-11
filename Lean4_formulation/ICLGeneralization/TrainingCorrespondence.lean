module

public import ICLGeneralization.StatisticalUniformTime

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem parent_index_of_pair (K J : ℕ) (k : Fin K) (j : Fin J) :
    parentIndex K J (finProdFinEquiv (k,j))=k := by simp [parentIndex]

theorem hierarchical_empirical_nested_sum {Θ X Ω : Type*} (K J N : ℕ) (f : Ω → ℝ)
    (s : HierarchicalTrainingSample Θ X Ω K J N) :
    hierarchicalEmpiricalLoss K J N f s =
      (∑ k : Fin K, ∑ j : Fin J, ∑ l : Fin N,
        f (s.2 (finProdFinEquiv (finProdFinEquiv (k,j),l))))/((K*J)*N:ℝ) := by
  classical
  unfold hierarchicalEmpiricalLoss sampleAverage
  have h := Equiv.sum_comp finProdFinEquiv (fun q : Fin ((K*J)*N) => f (s.2 q))
  rw [←h,Fintype.sum_prod_type]
  have h' := Equiv.sum_comp finProdFinEquiv (fun q : Fin (K*J) => ∑ l : Fin N, f (s.2 (finProdFinEquiv (q,l))))
  rw [←h',Fintype.sum_prod_type]
  simp only [Nat.cast_mul]

theorem episode_batch_conditional_law {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (K J : ℕ) (κ : Kernel Θ X) [IsMarkovKernel κ] (t : Fin K → Θ) :
    episodeBatchKernel K J κ t=Measure.pi (fun i => κ (t (parentIndex K J i))) := by
  simp only [episodeBatchKernel,independent_batch_kernel_apply,Kernel.comap_apply]

theorem diffusion_batch_conditional_law {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (κ : Kernel X Ω) [IsMarkovKernel κ] (x : Fin (K*J) → X) :
    diffusionBatchKernel K J N κ x=Measure.pi (fun i => κ (x (parentIndex (K*J) N i))) := by
  simp only [diffusionBatchKernel,episode_batch_conditional_law]

#print axioms parent_index_of_pair
#print axioms hierarchical_empirical_nested_sum
#print axioms episode_batch_conditional_law
#print axioms diffusion_batch_conditional_law
end GeneralizationCheck
