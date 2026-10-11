module

public import ICLGeneralization.Gaussian
public import ICLGeneralization.Analytic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

variable {V : Type*} [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V]

theorem compact_supported_continuous_integrable (μ : Measure V) [IsFiniteMeasure μ]
    (S : Set V) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S)
    (f : V → ℝ) (hf : Continuous f) : Integrable f μ := by
  have h := hf.continuousOn.integrableOn_compact hS (μ := μ)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hsupport] using h

theorem compact_kernel_integrable (μ : Measure V) [IsFiniteMeasure μ]
    (S : Set V) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S) (b : ℝ) (y : V) :
    Integrable (kernel b y) μ := by
  apply compact_supported_continuous_integrable μ S hS hsupport
  unfold kernel
  fun_prop

theorem compact_kernel_reciprocal_integrable (μ : Measure V) [IsFiniteMeasure μ]
    (S : Set V) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S) (b : ℝ) (y : V) :
    Integrable (fun x => 1/kernel b y x) μ := by
  apply compact_supported_continuous_integrable μ S hS hsupport
  have hk : Continuous (kernel b y) := by unfold kernel; fun_prop
  exact continuous_const.div hk (fun x => ne_of_gt (Real.exp_pos _))

theorem compact_kernel_mean_positive (μ : Measure V) [IsProbabilityMeasure μ]
    (S : Set V) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S) (b : ℝ) (y : V) :
    0 < ∫ x, kernel b y x ∂μ := by
  exact integral_exp_pos (compact_kernel_integrable μ S hS hsupport b y)

theorem compact_kernel_jensen (μ : Measure V) [IsProbabilityMeasure μ]
    (S : Set V) (hS : IsCompact S) (hsupport : ∀ᵐ x ∂μ, x ∈ S) (b : ℝ) (y : V) :
    1/(∫ x, kernel b y x ∂μ) ≤ ∫ x, 1/kernel b y x ∂μ := by
  apply integral_reciprocal_jensen μ (kernel b y)
    (compact_kernel_integrable μ S hS hsupport b y)
    (compact_kernel_reciprocal_integrable μ S hS hsupport b y)
  · exact Filter.Eventually.of_forall (fun x => Real.exp_pos _)
  · exact compact_kernel_mean_positive μ S hS hsupport b y

#print axioms compact_supported_continuous_integrable
#print axioms compact_kernel_integrable
#print axioms compact_kernel_reciprocal_integrable
#print axioms compact_kernel_mean_positive
#print axioms compact_kernel_jensen
end GeneralizationCheck
