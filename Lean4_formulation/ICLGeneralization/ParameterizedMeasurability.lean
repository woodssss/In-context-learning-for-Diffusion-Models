module

public import ICLGeneralization.HierarchicalTraining

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GeneralizationCheck

theorem parameterized_loss_continuous {ι Ω : Type*} [Fintype ι]
    (A : Set (ι → ℝ)) (f : (ι → ℝ) → Ω → ℝ) (K : Ω → ℝ) (hK : ∀ ω, 0≤K ω)
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0≤ε → (∀ p, |θ p-θ' p|≤ε) →
      ∀ ω, |f θ ω-f θ' ω|≤K ω*ε) (ω : Ω) : Continuous (fun θ : A => f θ.val ω) := by
  have h : LipschitzWith ⟨K ω,hK ω⟩ (fun θ : A => f θ.val ω) := by
    apply LipschitzWith.of_dist_le_mul
    intro θ θ'
    change |f θ.val ω-f θ'.val ω|≤K ω*dist θ θ'
    apply hLip θ.val θ.property θ'.val θ'.property (dist θ θ') dist_nonneg
    intro p
    have hd := dist_le_pi_dist θ.val θ'.val p
    simpa only [Real.dist_eq,Subtype.dist_eq] using hd
  exact h.continuous

theorem parameterized_loss_joint_measurable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (A : Set (ι → ℝ)) (f : (ι → ℝ) → Ω → ℝ) (K : Ω → ℝ) (hK : ∀ ω, 0≤K ω)
    (hf : ∀ θ ∈ A, Measurable (f θ))
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0≤ε → (∀ p, |θ p-θ' p|≤ε) →
      ∀ ω, |f θ ω-f θ' ω|≤K ω*ε) : Measurable (fun p : A × Ω => f p.1.val p.2) :=
  measurable_uncurry_of_continuous_of_measurable (parameterized_loss_continuous A f K hK hLip)
    (fun θ => hf θ.val θ.property)

theorem joint_kernel_average_measurable {P X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace X] [MeasurableSpace Ω]
    (f : P → Ω → ℝ) (κ : Kernel X Ω) [IsMarkovKernel κ]
    (hf : Measurable (fun p : P × Ω => f p.1 p.2)) :
    Measurable (fun p : P × X => ∫ ω, f p.1 ω ∂κ p.2) := by
  have h : Measurable (fun p : (P × X) × Ω => f p.1.1 p.2) :=
    hf.comp (measurable_fst.fst.prodMk measurable_snd)
  exact h.stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ.comap Prod.snd measurable_snd) |>.measurable

#print axioms parameterized_loss_continuous
#print axioms parameterized_loss_joint_measurable
#print axioms joint_kernel_average_measurable
end GeneralizationCheck
