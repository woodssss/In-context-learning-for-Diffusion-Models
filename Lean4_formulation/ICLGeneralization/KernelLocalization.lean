module

public import ICLGeneralization.MeasurablePartition

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem partition_ratio_with_zero_cells {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hz : ∀ i, b i=0 → a i=0) :
    (∑ i, a i)/(∑ i, b i) ≤ ∑ i, a i/b i := by
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hbi : b i=0
  · simp [hbi, hz i hbi]
  · exact div_le_div_of_nonneg_left (ha i) (lt_of_le_of_ne (hb i) (Ne.symm hbi))
      (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))

theorem zero_cell_population_ratio (D : ℕ) (μ : Measure (KernelSpace D))
    (A : Set (KernelSpace D)) (hA : μ A=0) (center : KernelSpace D → KernelSpace D) (β : ℝ) :
    populationKernelRatio D (ProbabilityTheory.cond μ A) center β = 0 := by
  funext y
  simp [populationKernelRatio, populationKernelSquared, populationKernel, ProbabilityTheory.cond,
    Measure.restrict_eq_zero.mpr hA]

theorem partition_population_ratio (D J : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (A : Fin J → Set (KernelSpace D)) (hA : ∀ j, MeasurableSet (A j))
    (hd : Pairwise (fun i j => Disjoint (A i) (A j))) (hunion : (⋃ j, A j) = S)
    (center : KernelSpace D → KernelSpace D) (hc : Continuous center) (β : ℝ) (y : KernelSpace D) :
    populationKernelRatio D μ center β y ≤
      ∑ j, populationKernelRatio D (ProbabilityTheory.cond μ (A j)) center β y := by
  have hi : Integrable (fun x => kernel β y (center x)) μ :=
    compact_supported_continuous_integrable μ S hS hsupport _ (by unfold kernel; fun_prop)
  have hi2 : Integrable (fun x => kernel β y (center x)^2) μ :=
    compact_supported_continuous_integrable μ S hS hsupport _ (by unfold kernel; fun_prop)
  unfold populationKernelRatio populationKernelSquared populationKernel
  rw [partition_integral_sum D J μ S hsupport A hA hd hunion _ hi2,
    partition_integral_sum D J μ S hsupport A hA hd hunion _ hi]
  calc
    _ ≤ ∑ j, (∫ x in A j, kernel β y (center x)^2 ∂μ)/(∫ x in A j, kernel β y (center x) ∂μ) := by
      apply partition_ratio_with_zero_cells
      · intro j
        exact integral_nonneg (fun _ => sq_nonneg _)
      · intro j
        exact integral_nonneg (fun _ => (Real.exp_pos _).le)
      · intro j hz
        have hmass : μ (A j)=0 := by
          by_contra hmass
          let : IsProbabilityMeasure (ProbabilityTheory.cond μ (A j)) := cond_isProbabilityMeasure hmass
          have hcondS : ∀ᵐ x ∂ProbabilityTheory.cond μ (A j), x ∈ S :=
            cond_absolutelyContinuous.ae_le hsupport
          have hp := compact_population_kernel_positive D (ProbabilityTheory.cond μ (A j))
            S hS hcondS center hc β y
          unfold populationKernel ProbabilityTheory.cond at hp
          rw [integral_smul_measure, hz, smul_zero] at hp
          exact (lt_irrefl 0) hp
        rw [Measure.restrict_eq_zero.mpr hmass, integral_zero_measure]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hm : μ (A j)=0
      · simp [Measure.restrict_eq_zero.mpr hm, ProbabilityTheory.cond]
      · exact conditional_integral_ratio D μ (A j) hm _ _

theorem conditional_ball_cell_bound (D : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (A : Set (KernelSpace D)) (hA : MeasurableSet A)
    (hsub : A ⊆ S) (c : KernelSpace D) (a s : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hball : A ⊆ Metric.closedBall c (s/2)) :
    Integrable (populationKernelRatio D (ProbabilityTheory.cond μ A) (fun x => a • x) (1/(2*s^2))) ∧
      (∫ y, populationKernelRatio D (ProbabilityTheory.cond μ A) (fun x => a • x) (1/(2*s^2)) y) ≤
        Real.exp 1*gaussianNormalizer D (1/(2*s^2)) := by
  by_cases hm : μ A=0
  · rw [zero_cell_population_ratio D μ A hm]
    constructor
    · exact integrable_zero _ _ _
    · simp only [Pi.zero_apply, integral_zero]
      exact (mul_pos (Real.exp_pos _) (gaussian_normalizer_positive D _ (by positivity))).le
  · let : IsProbabilityMeasure (ProbabilityTheory.cond μ A) := cond_isProbabilityMeasure hm
    apply gaussian_cell_integrated_bound D (ProbabilityTheory.cond μ A) S hS
      (conditional_cell_support D μ A S hA hsub) (fun x => a • x) (by fun_prop)
      (1/(2*s^2)) (by positivity)
    filter_upwards [conditional_cell_pair_support D μ A hA] with p hp
    exact scaled_ball_cell_diameter D A c a s ha hs hball p.1 p.2 hp.1 hp.2

theorem localized_kernel_ratio_integral (D J : ℕ) (μ : Measure (KernelSpace D)) [IsProbabilityMeasure μ]
    (S : Set (KernelSpace D)) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (c : Fin J → KernelSpace D) (a s : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ s/2) :
    Integrable (populationKernelRatio D μ (fun x => a • x) (1/(2*s^2))) ∧
      (∫ y, populationKernelRatio D μ (fun x => a • x) (1/(2*s^2)) y) ≤
        (J : ℝ)*Real.exp 1*gaussianNormalizer D (1/(2*s^2)) := by
  obtain ⟨A,hA,hsub,hball,hd,hunion⟩ := finite_ball_partition D J S hS.measurableSet c (s/2) hcover
  have hcell (j : Fin J) := conditional_ball_cell_bound D μ S hS (A j) (hA j) (hsub j)
    (c j) a s ha hs (hball j)
  have hsum : Integrable (fun y => ∑ j, populationKernelRatio D (ProbabilityTheory.cond μ (A j))
      (fun x => a • x) (1/(2*s^2)) y) := integrable_finsetSum _ (fun j _ => (hcell j).1)
  have hpoint := partition_population_ratio D J μ S hS hsupport A hA hd hunion
    (fun x => a • x) (by fun_prop) (1/(2*s^2))
  have hratio : Integrable (populationKernelRatio D μ (fun x => a • x) (1/(2*s^2))) := by
    apply Integrable.mono' hsum
      (measurable_population_kernel_ratio D μ (fun x => a • x) (by fun_prop) _).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun y => by
      have hnn : 0 ≤ populationKernelRatio D μ (fun x => a • x) (1/(2*s^2)) y := by
        unfold populationKernelRatio populationKernelSquared populationKernel
        exact div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => (Real.exp_pos _).le))
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hpoint y)
  refine ⟨hratio, ?_⟩
  calc
    _ ≤ ∫ y, ∑ j, populationKernelRatio D (ProbabilityTheory.cond μ (A j))
        (fun x => a • x) (1/(2*s^2)) y :=
      integral_mono_ae hratio hsum (Filter.Eventually.of_forall hpoint)
    _ = ∑ j, ∫ y, populationKernelRatio D (ProbabilityTheory.cond μ (A j))
        (fun x => a • x) (1/(2*s^2)) y := integral_finsetSum _ (fun j _ => (hcell j).1)
    _ ≤ ∑ _j : Fin J, Real.exp 1*gaussianNormalizer D (1/(2*s^2)) :=
      Finset.sum_le_sum (fun j _ => (hcell j).2)
    _ = _ := by simp; ring

#print axioms partition_ratio_with_zero_cells
#print axioms zero_cell_population_ratio
#print axioms partition_population_ratio
#print axioms conditional_ball_cell_bound
#print axioms localized_kernel_ratio_integral
end GeneralizationCheck
