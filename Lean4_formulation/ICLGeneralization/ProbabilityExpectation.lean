module

public import ICLGeneralization.RatioEstimator
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem bounded_probability_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Integrable f μ ∧ |∫ x, f x ∂μ| ≤ B := by
  have hi := (bounded_real_memLp μ f hf B hB 1).integrable (le_refl _)
  refine ⟨hi, ?_⟩
  calc
    _ = ‖∫ x, f x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x, B ∂μ := integral_mono_ae hi.norm (integrable_const _)
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hB x))
    _ = B := by simp

theorem integrated_bounded_measurable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : X × Ω → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ p, |f p| ≤ B) :
    Measurable (fun x => ∫ ω, f (x,ω) ∂μ) ∧
      (∀ x, Integrable (fun ω => f (x,ω)) μ) ∧
      (∀ x, |∫ ω, f (x,ω) ∂μ| ≤ B) := by
  exact ⟨hf.stronglyMeasurable.integral_prod_right'.measurable,
    fun x => (bounded_probability_integral μ _ (hf.comp ((measurable_const : Measurable (fun _ : Ω => x)).prodMk measurable_id)) B (fun ω => hB (x,ω))).1,
    fun x => (bounded_probability_integral μ _ (hf.comp ((measurable_const : Measurable (fun _ : Ω => x)).prodMk measurable_id)) B (fun ω => hB (x,ω))).2⟩

theorem probability_integral_nonnegative {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∫ x, f x ∂μ := integral_nonneg hf

#print axioms bounded_probability_integral
#print axioms integrated_bounded_measurable
#print axioms probability_integral_nonnegative
end GeneralizationCheck
