module

public import ICLGeneralization.NativeCoverMembership
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Integral

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def independentBatchKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] :
    (N : ℕ) → (Fin N → Kernel X Y) → Kernel X (Fin N → Y)
  | 0, _ => Kernel.const X (Measure.dirac (Fin.elim0 : Fin 0 → Y))
  | N+1, κ => ((κ 0).prod (independentBatchKernel N (fun i => κ i.succ))).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => Y) 0).symm

instance independent_batch_markov {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (N : ℕ) (κ : Fin N → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (independentBatchKernel N κ) := by
  induction N with
  | zero => dsimp only [independentBatchKernel]; infer_instance
  | succ N ih =>
    let : IsMarkovKernel (independentBatchKernel N (fun i => κ i.succ)) := ih _
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => Y) 0).symm.measurable

theorem independent_batch_kernel_apply {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (N : ℕ) (κ : Fin N → Kernel X Y) [∀ i, IsMarkovKernel (κ i)] (x : X) :
    independentBatchKernel N κ x = Measure.pi (fun i => κ i x) := by
  induction N with
  | zero => exact (Measure.pi_of_empty (fun i : Fin 0 => κ i x) (Fin.elim0 : Fin 0 → Y)).symm
  | succ N ih =>
    simp only [independentBatchKernel,Kernel.map_apply _
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => Y) 0).symm.measurable,Kernel.prod_apply,ih]
    exact (measurePreserving_piFinSuccAbove (fun i => κ i x) 0).symm.map_eq

noncomputable def populationAverage {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (μ : Fin N → Measure Y) (f : Y → ℝ) : ℝ := (∑ i, ∫ y, f y ∂μ i)/(N:ℝ)

noncomputable def sampleDeviation {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (μ : Fin N → Measure Y) (f : Y → ℝ) (x : Fin N → Y) : ℝ :=
  populationAverage N μ f-sampleAverage N f x

theorem independent_average_integral {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (f : Y → ℝ)
    (hf : ∀ i, Integrable f (μ i)) :
    ∫ x, sampleAverage N f x ∂Measure.pi μ = populationAverage N μ f := by
  have hev (i : Fin N) : (∫ x, f (x i) ∂Measure.pi μ) = ∫ y, f y ∂μ i := by
    have hm := measurePreserving_eval μ i
    have hfm : AEStronglyMeasurable f (Measure.map (Function.eval i) (Measure.pi μ)) := by
      rw [hm.map_eq]
      exact (hf i).aestronglyMeasurable
    have h := integral_map hm.measurable.aemeasurable hfm
    rw [hm.map_eq] at h
    exact h.symm
  unfold sampleAverage populationAverage
  rw [integral_div,integral_finsetSum]
  · simp_rw [hev]
  · intro i _
    exact (measurePreserving_eval μ i).integrable_comp_of_integrable (hf i)

theorem independent_average_abs_bound {Y : Type*} (N : ℕ) (hN : 0<N)
    (f : Y → ℝ) (M : ℝ) (hb : ∀ y, |f y|≤M) (x : Fin N → Y) :
    |sampleAverage N f x|≤M := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  unfold sampleAverage
  rw [abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  simpa only [mul_comm] using finite_sum_abs_bound N (fun i => f (x i)) M (fun i => hb _)

theorem independent_average_zero {Y : Type*} [MeasurableSpace Y] (N : ℕ)
    (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)] (f : Y → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ y, |f y|≤M) :
    (∫ x, sampleAverage N f x-populationAverage N μ f ∂Measure.pi μ)=0 := by
  have hi : Integrable (sampleAverage N f) (Measure.pi μ) := by
    unfold sampleAverage
    apply (integrable_finsetSum _ (fun i _ => (measurePreserving_eval μ i).integrable_comp_of_integrable
      ((bounded_probability_integral (μ i) f hf M hb).1))).div_const
  rw [integral_sub hi (integrable_const _),independent_average_integral N μ f
    (fun i => (bounded_probability_integral (μ i) f hf M hb).1)]
  simp

#print axioms independent_batch_kernel_apply
#print axioms independent_average_integral
#print axioms independent_average_abs_bound
#print axioms independent_average_zero
end GeneralizationCheck
