module

public import ICLGeneralization.GaussianCellIntegration
public import ICLGeneralization.Core
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Order.Disjointed

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem finite_measurable_disjointification {V : Type*} [MeasurableSpace V] (J : ℕ)
    (B : Fin J → Set V) (hB : ∀ j, MeasurableSet (B j)) :
    (∀ j, MeasurableSet (disjointed B j)) ∧
    (∀ j, disjointed B j ⊆ B j) ∧ Pairwise (fun i j => Disjoint (disjointed B i) (disjointed B j)) ∧
    (⋃ j, disjointed B j) = ⋃ j, B j := by
  refine ⟨?_, disjointed_subset B, disjoint_disjointed B, iUnion_disjointed⟩
  intro j
  rw [disjointed_eq_inter_compl]
  exact (hB j).inter (MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ => (hB i).compl)))

theorem finite_ball_partition (D J : ℕ) (S : Set (KernelSpace D)) (hS : MeasurableSet S)
    (c : Fin J → KernelSpace D) (r : ℝ)
    (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ r) :
    ∃ A : Fin J → Set (KernelSpace D),
      (∀ j, MeasurableSet (A j)) ∧ (∀ j, A j ⊆ S) ∧
      (∀ j, A j ⊆ Metric.closedBall (c j) r) ∧ Pairwise (fun i j => Disjoint (A i) (A j)) ∧ (⋃ j, A j) = S := by
  let B := fun j => S ∩ Metric.closedBall (c j) r
  have h := finite_measurable_disjointification J B (fun j => hS.inter measurableSet_closedBall)
  refine ⟨disjointed B, h.1, ?_, ?_, h.2.2.1, ?_⟩
  · intro j x hx
    exact (h.2.1 j hx).1
  · intro j x hx
    exact (h.2.1 j hx).2
  · rw [h.2.2.2]
    ext x
    simp only [Set.mem_iUnion, B, Set.mem_inter_iff, Metric.mem_closedBall]
    exact ⟨fun ⟨_, hx, _⟩ => hx, fun hx => by obtain ⟨j,hj⟩ := hcover x hx; exact ⟨j,hx,hj⟩⟩

theorem partition_integral_sum (D J : ℕ) (μ : Measure (KernelSpace D))
    (S : Set (KernelSpace D)) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (A : Fin J → Set (KernelSpace D)) (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hunion : (⋃ j, A j) = S)
    (f : KernelSpace D → ℝ) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑ j, ∫ x in A j, f x ∂μ := by
  rw [← integral_iUnion_fintype hA hd (fun _ => hf.integrableOn), hunion,
    Measure.restrict_eq_self_of_ae_mem hsupport]

theorem conditional_integral_ratio (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (A : Set (KernelSpace D)) (hA : μ A ≠ 0) (f g : KernelSpace D → ℝ) :
    (∫ x in A, f x ∂μ)/(∫ x in A, g x ∂μ) =
      (∫ x, f x ∂cond μ A)/(∫ x, g x ∂cond μ A) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure]
  simp only [smul_eq_mul]
  exact (cell_mass_cancellation ((μ A)⁻¹).toReal _ _
    (ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr (measure_ne_top μ A),
      ENNReal.inv_ne_top.mpr hA⟩)).symm

theorem conditional_cell_support (D : ℕ) (μ : Measure (KernelSpace D))
    (A S : Set (KernelSpace D)) (hA : MeasurableSet A) (hsub : A ⊆ S) :
    ∀ᵐ x ∂cond μ A, x ∈ S := ae_cond_of_forall_mem hA (fun _ hx => hsub hx)

theorem conditional_cell_pair_support (D : ℕ) (μ : Measure (KernelSpace D)) [IsFiniteMeasure μ]
    (A : Set (KernelSpace D)) (hA : MeasurableSet A) :
    ∀ᵐ p ∂(cond μ A).prod (cond μ A), p.1 ∈ A ∧ p.2 ∈ A := by
  apply (Measure.ae_prod_iff_ae_ae (hA.preimage measurable_fst |>.inter (hA.preimage measurable_snd))).2
  filter_upwards [ae_cond_mem hA] with x hx
  filter_upwards [ae_cond_mem hA] with z hz
  exact ⟨hx,hz⟩

theorem scaled_ball_cell_diameter (D : ℕ) (A : Set (KernelSpace D)) (c : KernelSpace D)
    (a s : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s) (hA : A ⊆ Metric.closedBall c (s/2))
    (x z : KernelSpace D) (hx : x ∈ A) (hz : z ∈ A) :
    2*(1/(2*s^2))*‖a • x-a • z‖^2 ≤ 1 := by
  have hx' : dist x c ≤ s/2 := hA hx
  have hz' : dist z c ≤ s/2 := hA hz
  have hdist : ‖x-z‖ ≤ s := by
    have h := dist_triangle x c z
    rw [dist_comm c z] at h
    rw [dist_eq_norm] at h
    linarith
  have hnorm : ‖a • x-a • z‖ ≤ s := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) ha.2).trans hdist
  have hsq : ‖a • x-a • z‖^2 ≤ s^2 := by nlinarith [norm_nonneg (a • x-a • z)]
  have h := div_le_one (sq_pos_of_pos hs) |>.2 hsq
  convert h using 1
  ring

#print axioms finite_measurable_disjointification
#print axioms finite_ball_partition
#print axioms partition_integral_sum
#print axioms conditional_integral_ratio
#print axioms conditional_cell_support
#print axioms conditional_cell_pair_support
#print axioms scaled_ball_cell_diameter
end GeneralizationCheck
