module

public import ICLGeneralization.LemmaFive
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GeneralizationCheck

noncomputable def coordinateShift (D : ℕ) (y : KernelSpace D) (j : Fin D) (u : ℝ) : KernelSpace D :=
  y+u • EuclideanSpace.single j 1

theorem coordinate_shift_at_zero (D : ℕ) (y : KernelSpace D) (j : Fin D) :
    coordinateShift D y j 0 = y := by simp [coordinateShift]

theorem coordinate_shift_component (D : ℕ) (y : KernelSpace D) (j : Fin D) (u : ℝ) :
    coordinateShift D y j u j = y j+u := by simp [coordinateShift, PiLp.add_apply, PiLp.smul_apply]

theorem gaussian_kernel_coordinate_derivative (D : ℕ) (β : ℝ) (y x : KernelSpace D)
    (j : Fin D) (u : ℝ) :
    HasDerivAt (fun v => kernel β (coordinateShift D y j v) x)
      ((-2*β)*(y j+u-x j)*kernel β (coordinateShift D y j u) x) u := by
  have hvec : HasDerivAt (fun v => coordinateShift D y j v-x) (EuclideanSpace.single j 1) u := by
    simpa [coordinateShift] using
      ((hasDerivAt_const u y).add ((hasDerivAt_id u).smul_const (EuclideanSpace.single j 1))).sub_const x
  have h := ((hvec.norm_sq).const_mul (-β)).exp
  convert h using 1
  · rfl
  · simp only [EuclideanSpace.inner_single_right, one_mul, starRingEnd_apply,
      PiLp.sub_apply, coordinate_shift_component, star_trivial]
    unfold kernel
    ring

noncomputable def supportQueryDensity {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (y : KernelSpace D) : ℝ :=
  (∫ x, sampleWeight a s y x ∂μ)/gaussianNormalizer D (1/(2*s^2))

noncomputable def trueGaussianScore {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (y : KernelSpace D) (j : Fin D) : ℝ :=
  deriv (fun u => Real.log (supportQueryDensity μ a s (coordinateShift D y j u))) 0

theorem log_query_density_coordinate_derivative (D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) [IsProbabilityMeasure μ] (b a s : ℝ) (hb : 0 ≤ b)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (y : KernelSpace D) (j : Fin D) :
    HasDerivAt (fun u => Real.log (supportQueryDensity μ a s (coordinateShift D y j u)))
      (posteriorScore μ a s y j) 0 := by
  let β := 1/(2*s^2)
  have hβ : 0 < β := by dsimp [β]; positivity
  let F := fun u (x : S) => sampleWeight a s (coordinateShift D y j u) x
  let F' := fun u (x : S) => (-2*β)*(y j+u-a*x.val j)*F u x
  have hdiff (u : ℝ) (x : S) : HasDerivAt (fun v => F v x) (F' u x) u := by
    have h := gaussian_kernel_coordinate_derivative D β y (a • x.val) j u
    simpa only [PiLp.smul_apply, smul_eq_mul, F, F', sampleWeight, β] using h
  have hFmeas (u : ℝ) : Measurable (F u) := measurable_fixed_sample_weight a s _
  have hF' : Measurable (F' 0) := by
    unfold F'
    exact ((measurable_const.sub ((measurable_clean_coordinate j).const_mul a)).const_mul _).mul (hFmeas 0)
  have hbound : ∀ x : S, ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      ‖F' u x‖ ≤ 2*β*(|y j|+1+b) := by
    intro x u hu
    have hcoord : |x.val j| ≤ b := abs_le.mpr (hbox x.val x.property j)
    have hau : |a*x.val j| ≤ b := by
      rw [abs_mul, abs_of_nonneg ha.1]
      exact (mul_le_mul ha.2 hcoord (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2.le⟩
    have hd : |y j+u-a*x.val j| ≤ |y j|+1+b := by
      calc
        _ ≤ |y j+u|+|a*x.val j| := abs_sub _ _
        _ ≤ |y j|+|u|+b := add_le_add (abs_add_le _ _) hau
        _ ≤ _ := by linarith
    have hw : |F u x| ≤ 1 := by
      rw [abs_of_pos (sample_weight_bounds a s _ x).1]
      exact (sample_weight_bounds a s _ x).2
    change |(-2*β)*(y j+u-a*x.val j)*F u x| ≤ _
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hβ]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left hd (by positivity)) hw (abs_nonneg _)
      (by positivity)).trans_eq (by ring)
  have hwLp (u : ℝ) : MemLp (F u) 2 μ := bounded_real_memLp μ _ (hFmeas u) 1
    (fun x => by rw [abs_of_pos (sample_weight_bounds a s _ x).1]; exact (sample_weight_bounds a s _ x).2) 2
  have hpop := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall (fun u => (hFmeas u).aestronglyMeasurable))
    ((hwLp 0).integrable (by norm_num)) hF'.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) (integrable_const _)
    (Filter.Eventually.of_forall (fun x u _ => hdiff u x))
  have hzero : F 0 = sampleWeight a s y := by funext x; simp [F, coordinate_shift_at_zero]
  have hm : 0 < ∫ x, sampleWeight a s y x ∂μ := positive_population_weight μ _
    (by simpa only [hzero] using (hwLp 0).integrable (by norm_num)) (fun x => (sample_weight_bounds a s y x).1)
  have hwx : Integrable (fun x : S => sampleWeight a s y x*x.val j) μ := by
    apply (bounded_real_memLp μ _ ((measurable_fixed_sample_weight a s y).mul (measurable_clean_coordinate j)) b _ 1).integrable (le_refl _)
    intro x
    change |sampleWeight a s y x*x.val j| ≤ b
    rw [abs_mul, abs_of_pos (sample_weight_bounds a s y x).1]
    exact (mul_le_mul (sample_weight_bounds a s y x).2 (abs_le.mpr (hbox x.val x.property j))
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hwint : Integrable (sampleWeight a s y) μ := by simpa only [hzero] using (hwLp 0).integrable (by norm_num)
  have hderiv : (∫ x, F' 0 x ∂μ) = (-2*β*y j)*(∫ x, sampleWeight a s y x ∂μ)+
      (2*β*a)*(∫ x, sampleWeight a s y x*x.val j ∂μ) := by
    have he (x : S) : F' 0 x = (-2*β*y j)*sampleWeight a s y x+(2*β*a)*(sampleWeight a s y x*x.val j) := by
      simp only [F', hzero]
      ring
    simp_rw [he]
    rw [integral_add (hwint.const_mul _) (hwx.const_mul _), integral_const_mul, integral_const_mul]
  have hp := (hpop.2.div_const (gaussianNormalizer D β)).log
    (show (∫ x, F 0 x ∂μ)/gaussianNormalizer D β ≠ 0 from ne_of_gt
      (div_pos (by simpa only [hzero] using hm) (gaussian_normalizer_positive D β hβ)))
  have hzβ : gaussianNormalizer D β ≠ 0 := ne_of_gt (gaussian_normalizer_positive D β hβ)
  have hcancel (v : ℝ) : v/gaussianNormalizer D β/((∫ x, sampleWeight a s y x ∂μ)/gaussianNormalizer D β) =
      v/(∫ x, sampleWeight a s y x ∂μ) := by
    have hn := ne_of_gt hm
    field_simp
  simp only [hzero, hcancel] at hp
  convert hp using 1
  · rfl
  · rw [hderiv]
    unfold posteriorScore kernelModelMean weightedMean
    dsimp only [β]
    have hn := ne_of_gt hm
    field_simp

theorem true_gaussian_score_eq_posterior (D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (b a s : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (y : KernelSpace D) (j : Fin D) :
    trueGaussianScore μ a s y j = posteriorScore μ a s y j :=
  (log_query_density_coordinate_derivative D S μ b a s hb ha hs hbox y j).deriv

#print axioms coordinate_shift_at_zero
#print axioms coordinate_shift_component
#print axioms gaussian_kernel_coordinate_derivative
#print axioms log_query_density_coordinate_derivative
#print axioms true_gaussian_score_eq_posterior
end GeneralizationCheck
