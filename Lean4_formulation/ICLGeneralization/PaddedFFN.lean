module

public import ICLGeneralization.ClippingFFN

@[expose] public section

open Matrix
namespace GeneralizationCheck

structure SixLayerFFN (d w : ℕ) where
  input : Matrix (Fin w) (Fin d) ℝ
  inputBias : Fin w → ℝ
  hidden : Matrix (Fin w) (Fin w) ℝ
  hiddenBias : Fin w → ℝ
  output : Matrix (Fin d) (Fin w) ℝ
  outputBias : Fin d → ℝ

noncomputable def SixLayerFFN.eval {d w : ℕ} (F : SixLayerFFN d w) (h : Fin d → ℝ) :
    Fin d → ℝ :=
  let first := fun r => max 0 (F.input.mulVec h r+F.inputBias r)
  let step := fun v r => max 0 (F.hidden.mulVec v r+F.hiddenBias r)
  fun r => F.output.mulVec ((step^[4]) first) r+F.outputBias r

noncomputable def zeroSixFFN (d w : ℕ) : SixLayerFFN d w where
  input := 0
  inputBias := 0
  hidden := 0
  hiddenBias := 0
  output := 0
  outputBias := 0

theorem zero_six_ffn_eval (d w : ℕ) (h : Fin d → ℝ) : (zeroSixFFN d w).eval h = 0 := by
  funext r
  simp [SixLayerFFN.eval, zeroSixFFN]

noncomputable def paddedClippingFFN {d : ℕ} (k : ℕ) (j : Fin d) (b : ℝ) :
    SixLayerFFN d (4+k) where
  input r c := Fin.addCases (fun p => clippingInputMatrix j p c) (fun _ => 0) r
  inputBias := Fin.addCases (clippingInputBias b) (fun _ => 0)
  hidden := 1
  hiddenBias := 0
  output r c := Fin.addCases (fun p => clippingOutputMatrix j r p) (fun _ => 0) c
  outputBias := clippingOutputBias j b

theorem padded_clipping_ffn_eval {d : ℕ} (k : ℕ) (j : Fin d) (b : ℝ) (h : Fin d → ℝ) :
    (paddedClippingFFN k j b).eval h = sixLayerClippingFFN j b h := by
  let first : Fin (4+k) → ℝ := Fin.addCases (clippingFirstHidden j b h) (fun _ => 0)
  have hfirst : (fun r => max 0 ((paddedClippingFFN k j b).input.mulVec h r+
      (paddedClippingFFN k j b).inputBias r)) = first := by
    funext r
    refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simp [paddedClippingFFN, Matrix.mulVec, dotProduct, first, clippingFirstHidden]
    · simp [paddedClippingFFN, Matrix.mulVec, dotProduct, first]
  have hfixed : (fun v r => max 0 ((paddedClippingFFN k j b).hidden.mulVec v r+
      (paddedClippingFFN k j b).hiddenBias r)) first = first := by
    funext r
    simp only [paddedClippingFFN, Matrix.one_mulVec, Pi.zero_apply, add_zero]
    apply max_eq_right
    refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simp only [first, Fin.addCases_left, clippingFirstHidden]
      exact le_max_left _ _
    · simp [first]
  funext r
  unfold SixLayerFFN.eval
  rw [hfirst, Function.iterate_fixed hfixed]
  unfold sixLayerClippingFFN
  rw [clipping_hidden_padding_exact]
  simp only [paddedClippingFFN, Matrix.mulVec, dotProduct, Fin.sum_univ_add,
    first, Fin.addCases_left, Fin.addCases_right, mul_zero, Finset.sum_const_zero, add_zero]

theorem padded_clipping_residual {d : ℕ} (k : ℕ) (j : Fin d) (b : ℝ)
    (hb : 0 ≤ b) (h : Fin d → ℝ) :
    h j+(paddedClippingFFN k j b).eval h j = max (-b) (min (h j) b) := by
  rw [padded_clipping_ffn_eval]
  exact six_layer_residual_clipping j b hb h

def SixLayerFFN.Bounded {d w : ℕ} (F : SixLayerFFN d w) (κ : ℝ) : Prop :=
  (∀ r c, |F.input r c| ≤ κ) ∧ (∀ r, |F.inputBias r| ≤ κ) ∧
  (∀ r c, |F.hidden r c| ≤ κ) ∧ (∀ r, |F.hiddenBias r| ≤ κ) ∧
  (∀ r c, |F.output r c| ≤ κ) ∧ (∀ r, |F.outputBias r| ≤ κ)

theorem zero_six_ffn_bounded (d w : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    (zeroSixFFN d w).Bounded κ := by
  simp [SixLayerFFN.Bounded, zeroSixFFN, hκ]

theorem padded_clipping_ffn_bounded {d : ℕ} (k : ℕ) (j : Fin d)
    (b κ : ℝ) (hκ : 1 ≤ κ) (hb : |b| ≤ κ) :
    (paddedClippingFFN k j b).Bounded κ := by
  classical
  have hzero : |(0 : ℝ)| ≤ κ := by norm_num; linarith
  have hin (r : Fin 4) (c : Fin d) : |clippingInputMatrix j r c| ≤ κ := by
    fin_cases r <;> simpa [clippingInputMatrix] using (read_row_abs_bound j c).trans hκ
  have hout (r : Fin d) (c : Fin 4) : |clippingOutputMatrix j r c| ≤ κ := by
    unfold clippingOutputMatrix
    split_ifs
    · fin_cases c <;> norm_num <;> exact hκ
    · exact hzero
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r c
    refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simpa only [paddedClippingFFN, Fin.addCases_left] using hin r c
    · simpa only [paddedClippingFFN, Fin.addCases_right] using hzero
  · intro r
    refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · fin_cases r
      · simpa [paddedClippingFFN, clippingInputBias] using hb
      · simpa [paddedClippingFFN, clippingInputBias] using hb
      · simpa [paddedClippingFFN, clippingInputBias] using hzero
      · simpa [paddedClippingFFN, clippingInputBias] using hzero
    · simpa only [paddedClippingFFN, Fin.addCases_right] using hzero
  · intro r c
    change |(1 : Matrix (Fin (4+k)) (Fin (4+k)) ℝ) r c| ≤ κ
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num <;> linarith
  · intro r
    exact hzero
  · intro r c
    refine Fin.addCases (fun c => ?_) (fun c => ?_) c
    · simpa only [paddedClippingFFN, Fin.addCases_left] using hout r c
    · simpa only [paddedClippingFFN, Fin.addCases_right] using hzero
  · intro r
    change |if r=j then -b else 0| ≤ κ
    split_ifs
    · simpa only [abs_neg] using hb
    · exact hzero

#print axioms zero_six_ffn_eval
#print axioms padded_clipping_ffn_eval
#print axioms padded_clipping_residual
#print axioms zero_six_ffn_bounded
#print axioms padded_clipping_ffn_bounded
end GeneralizationCheck
