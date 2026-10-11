module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

@[expose] public section

namespace GeneralizationCheck

noncomputable def softmaxReadout (n : ℕ) (score value : Fin n → ℝ) : ℝ :=
  (∑ i, value i*Real.exp (score i))/(∑ i, Real.exp (score i))

theorem softmax_denominator_positive (n : ℕ) (hn : 0 < n) (score : Fin n → ℝ) :
    0 < ∑ i, Real.exp (score i) := by
  apply Finset.sum_pos
  · intro i _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩

theorem softmax_readout_is_attention (n : ℕ) (score value : Fin n → ℝ) :
    (∑ i, (Real.exp (score i)/(∑ k, Real.exp (score k)))*value i) =
      softmaxReadout n score value := by
  unfold softmaxReadout
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem softmax_shift_cancellation (n : ℕ) (score value : Fin n → ℝ) (M : ℝ) :
    softmaxReadout n (fun i => M+score i) value = softmaxReadout n score value := by
  unfold softmaxReadout
  simp_rw [Real.exp_add]
  have hnum : (∑ i, value i*(Real.exp M*Real.exp (score i))) =
      Real.exp M*(∑ i, value i*Real.exp (score i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hnum, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt (Real.exp_pos M))

theorem softmax_readout_bounds (n : ℕ) (hn : 0 < n) (score value : Fin n → ℝ)
    (b : ℝ) (hv : ∀ i, -b ≤ value i ∧ value i ≤ b) :
    -b ≤ softmaxReadout n score value ∧ softmaxReadout n score value ≤ b := by
  have hden := softmax_denominator_positive n hn score
  unfold softmaxReadout
  constructor
  · apply (le_div_iff₀ hden).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hv i).1 (Real.exp_nonneg _)
  · apply (div_le_iff₀ hden).2
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hv i).2 (Real.exp_nonneg _)

noncomputable def clippingCorrection (b z : ℝ) : ℝ :=
  -b+max 0 (z+b)-max 0 (z-b)-max 0 z+max 0 (-z)

theorem clipping_residual (b z : ℝ) (hb : 0 ≤ b) :
    z+clippingCorrection b z = max (-b) (min z b) := by
  have hid : -max 0 z+max 0 (-z) = -z := by
    by_cases hz : 0 ≤ z
    · rw [max_eq_right hz, max_eq_left (by linarith : -z ≤ 0)]
      ring
    · have hz' : z ≤ 0 := le_of_not_ge hz
      rw [max_eq_left hz', max_eq_right (by linarith : 0 ≤ -z)]
      ring
  unfold clippingCorrection
  have he : z+(-b+max 0 (z+b)-max 0 (z-b)-max 0 z+max 0 (-z)) =
      -b+max 0 (z+b)-max 0 (z-b) := by linarith
  rw [he]
  by_cases hlo : z ≤ -b
  · rw [max_eq_left (by linarith : z+b ≤ 0), max_eq_left (by linarith : z-b ≤ 0),
      min_eq_left (by linarith : z ≤ b), max_eq_left hlo]
    ring
  · by_cases hhi : b ≤ z
    · rw [max_eq_right (by linarith : 0 ≤ z+b), max_eq_right (by linarith : 0 ≤ z-b),
        min_eq_right hhi, max_eq_right (by linarith : -b ≤ b)]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ z+b), max_eq_left (by linarith : z-b ≤ 0),
        min_eq_left (le_of_not_ge hhi), max_eq_right (by linarith : -b ≤ z)]
      ring

theorem clipping_global_bounds (b z : ℝ) (hb : 0 ≤ b) :
    -b ≤ z+clippingCorrection b z ∧ z+clippingCorrection b z ≤ b := by
  rw [clipping_residual b z hb]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem clipping_preserves_bounded_value (b z : ℝ) (hz : -b ≤ z ∧ z ≤ b) :
    z+clippingCorrection b z = z := by
  have hb : 0 ≤ b := by linarith
  rw [clipping_residual b z hb, min_eq_left hz.2, max_eq_right hz.1]

theorem clipped_softmax_exact (n : ℕ) (hn : 0 < n) (score value : Fin n → ℝ)
    (M b : ℝ) (hv : ∀ i, -b ≤ value i ∧ value i ≤ b) :
    softmaxReadout n (fun i => M+score i) value+
      clippingCorrection b (softmaxReadout n (fun i => M+score i) value) =
        softmaxReadout n score value := by
  rw [clipping_preserves_bounded_value b _ (softmax_readout_bounds n hn _ value b hv)]
  exact softmax_shift_cancellation n score value M

#print axioms softmax_denominator_positive
#print axioms softmax_readout_is_attention
#print axioms softmax_shift_cancellation
#print axioms softmax_readout_bounds
#print axioms clipping_residual
#print axioms clipping_global_bounds
#print axioms clipping_preserves_bounded_value
#print axioms clipped_softmax_exact
end GeneralizationCheck
