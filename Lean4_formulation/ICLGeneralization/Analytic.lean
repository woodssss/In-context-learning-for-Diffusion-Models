module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

/- Jensen for reciprocal, proved directly from its supporting line.
   The mean's positivity and both integrability obligations are explicit. -/
theorem reciprocal_supporting_line (u m : ℝ) (hu : 0 < u) (hm : 0 < m) :
    2/m-u/m^2 ≤ 1/u := by
  apply (le_div_iff₀ hu).2
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hm)).mp
  field_simp
  nlinarith [sq_nonneg (u-m)]

theorem integral_reciprocal_jensen {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hi : Integrable (fun x => 1/f x) μ)
    (hp : ∀ᵐ x ∂μ, 0 < f x) (hm : 0 < ∫ x, f x ∂μ) :
    1/(∫ x, f x ∂μ) ≤ ∫ x, 1/f x ∂μ := by
  let m := ∫ x, f x ∂μ
  have ht : Integrable (fun x => 2/m-f x/m^2) μ :=
    (integrable_const _).sub (hf.div_const _)
  have hle : ∀ᵐ x ∂μ, 2/m-f x/m^2 ≤ 1/f x := by
    filter_upwards [hp] with x hx
    exact reciprocal_supporting_line (f x) m hx hm
  have h := integral_mono_ae ht hi hle
  rw [integral_sub (integrable_const _) (hf.div_const _),
      integral_const, integral_div] at h
  simp only [probReal_univ, one_smul] at h
  have he : 2/m-m/m^2 = 1/m := by
    have hmn : m ≠ 0 := ne_of_gt hm
    field_simp
    ring
  change 2/m-m/m^2 ≤ _ at h
  rw [he] at h
  exact h

#print axioms reciprocal_supporting_line
#print axioms integral_reciprocal_jensen
end GeneralizationCheck
