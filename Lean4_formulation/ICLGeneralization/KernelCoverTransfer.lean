module

public import ICLGeneralization.GeneralNetworkMeasurability
public import ICLGeneralization.UniformFunctionCover

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
variable {ι Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

noncomputable def averagedFamily (f : (ι → ℝ) → Ω → ℝ) (κ : Kernel X Ω)
    (θ : ι → ℝ) (x : X) : ℝ := ∫ ω, f θ ω ∂κ x

theorem kernel_average_measurable (f : (ι → ℝ) → Ω → ℝ) (κ : Kernel X Ω)
    [IsMarkovKernel κ] (θ : ι → ℝ) (hf : Measurable (f θ)) : Measurable (averagedFamily f κ θ) := by
  exact (hf.comp (measurable_snd : Measurable (Prod.snd : X × Ω → Ω))).stronglyMeasurable.integral_kernel_prod_right' |>.measurable

theorem kernel_average_bounded (f : (ι → ℝ) → Ω → ℝ) (κ : Kernel X Ω)
    [IsMarkovKernel κ] (θ : ι → ℝ) (hf : Measurable (f θ)) (M : ℝ) (hb : ∀ ω, |f θ ω| ≤ M)
    (x : X) : |averagedFamily f κ θ x| ≤ M :=
  (bounded_probability_integral (κ x) (f θ) hf M hb).2

theorem kernel_average_distance (f : (ι → ℝ) → Ω → ℝ) (κ : Kernel X Ω)
    [IsMarkovKernel κ] (θ θ' : ι → ℝ) (hf : Measurable (f θ)) (hf' : Measurable (f θ'))
    (M E : ℝ) (hb : ∀ ω, |f θ ω| ≤ M) (hb' : ∀ ω, |f θ' ω| ≤ M)
    (hd : ∀ ω, |f θ ω-f θ' ω| ≤ E) (x : X) :
    |averagedFamily f κ θ x-averagedFamily f κ θ' x| ≤ E := by
  have hi := (bounded_probability_integral (κ x) (f θ) hf M hb).1
  have hi' := (bounded_probability_integral (κ x) (f θ') hf' M hb').1
  have hd' := (bounded_probability_integral (κ x) (fun ω => f θ ω-f θ' ω) (hf.sub hf') E hd).2
  rwa [integral_sub hi hi'] at hd'

theorem kernel_average_parameter_stability (A : Set (ι → ℝ)) (f : (ι → ℝ) → Ω → ℝ)
    (κ : Kernel X Ω) [IsMarkovKernel κ] (K M : ℝ)
    (hf : ∀ θ ∈ A, Measurable (f θ)) (hb : ∀ θ ∈ A, ∀ ω, |f θ ω| ≤ M)
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ p, |θ p-θ' p| ≤ ε) →
      ∀ ω, |f θ ω-f θ' ω| ≤ K*ε) :
    ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ p, |θ p-θ' p| ≤ ε) →
      ∀ x, |averagedFamily f κ θ x-averagedFamily f κ θ' x| ≤ K*ε := by
  intro θ hθ θ' hθ' ε hε he x
  exact kernel_average_distance f κ θ θ' (hf θ hθ) (hf θ' hθ') M (K*ε)
    (hb θ hθ) (hb θ' hθ') (hLip θ hθ θ' hθ' ε hε he) x

#print axioms kernel_average_measurable
#print axioms kernel_average_bounded
#print axioms kernel_average_distance
#print axioms kernel_average_parameter_stability
end GeneralizationCheck
