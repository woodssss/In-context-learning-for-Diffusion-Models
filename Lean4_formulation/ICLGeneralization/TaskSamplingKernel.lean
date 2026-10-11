module

public import ICLGeneralization.ProbabilityExpectation
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

variable {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]

noncomputable def iidPromptKernel (n : ℕ) (ρ : Kernel Θ X) : Kernel Θ (Fin n → X) :=
  match n with
  | 0 => Kernel.const Θ (Measure.dirac (Fin.elim0 : Fin 0 → X))
  | k+1 => (ρ.prod (iidPromptKernel k ρ)).map
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k+1) => X) 0).symm

instance (n : ℕ) (ρ : Kernel Θ X) [IsMarkovKernel ρ] : IsMarkovKernel (iidPromptKernel n ρ) := by
  induction n with
  | zero => dsimp only [iidPromptKernel]; infer_instance
  | succ n ih =>
    let : IsMarkovKernel (iidPromptKernel n ρ) := ih
    exact Kernel.IsMarkovKernel.map _ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurable

theorem iid_prompt_kernel_apply (n : ℕ) (ρ : Kernel Θ X) [IsMarkovKernel ρ] (θ : Θ) :
    iidPromptKernel n ρ θ = promptLaw n (ρ θ) := by
  induction n with
  | zero =>
    exact (Measure.pi_of_empty (fun _ : Fin 0 => ρ θ) (Fin.elim0 : Fin 0 → X)).symm
  | succ n ih =>
    simp only [iidPromptKernel, Kernel.map_apply _
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => X) 0).symm.measurable,
      Kernel.prod_apply, ih]
    exact (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ρ θ) 0).symm.map_eq

theorem measurable_prompt_expectation {Y : Type*} [MeasurableSpace Y] (n : ℕ) (ρ : Kernel Θ X)
    [IsMarkovKernel ρ] (f : (Θ × Y) × (Fin n → X) → ℝ) (hf : Measurable f) :
    Measurable (fun p : Θ × Y => ∫ ω, f (p,ω) ∂promptLaw n (ρ p.1)) := by
  have h := hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := (iidPromptKernel n ρ).comap Prod.fst measurable_fst) |>.measurable
  simpa only [Kernel.comap_apply, iid_prompt_kernel_apply] using h

theorem measurable_task_expectation (ρ : Kernel Θ X) [IsMarkovKernel ρ]
    (f : Θ × X → ℝ) (hf : Measurable f) :
    Measurable (fun θ => ∫ x, f (θ,x) ∂ρ θ) :=
  hf.stronglyMeasurable.integral_kernel_prod_right' |>.measurable

#print axioms iid_prompt_kernel_apply
#print axioms measurable_prompt_expectation
#print axioms measurable_task_expectation
end GeneralizationCheck
