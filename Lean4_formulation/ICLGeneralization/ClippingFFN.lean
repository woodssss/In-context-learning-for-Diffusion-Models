module

public import ICLGeneralization.MatrixSelection
public import ICLGeneralization.RealizationReadout

@[expose] public section

open Matrix
namespace GeneralizationCheck

noncomputable def clippingInputMatrix {d : ℕ} (j : Fin d) : Matrix (Fin 4) (Fin d) ℝ :=
  fun r c => ![1,1,1,-1] r*readRow j c

noncomputable def clippingInputBias (b : ℝ) : Fin 4 → ℝ := ![b,-b,0,0]

theorem clipping_input_matrix_action {d : ℕ} (j : Fin d) (h : Fin d → ℝ) (r : Fin 4) :
    (clippingInputMatrix j).mulVec h r = ![1,1,1,-1] r*h j := by
  unfold Matrix.mulVec dotProduct clippingInputMatrix
  simp only [mul_assoc]
  rw [← Finset.mul_sum, read_row_action]

noncomputable def clippingFirstHidden {d : ℕ} (j : Fin d) (b : ℝ) (h : Fin d → ℝ) : Fin 4 → ℝ :=
  fun r => max 0 ((clippingInputMatrix j).mulVec h r+clippingInputBias b r)

noncomputable def clippingIdentityHidden (h : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun r => max 0 ((1 : Matrix (Fin 4) (Fin 4) ℝ).mulVec h r)

theorem clipping_identity_hidden_fixed (h : Fin 4 → ℝ) (hh : ∀ r, 0 ≤ h r) :
    clippingIdentityHidden h = h := by
  funext r
  unfold clippingIdentityHidden
  rw [Matrix.one_mulVec, max_eq_right (hh r)]

theorem clipping_hidden_padding_exact {d : ℕ} (j : Fin d) (b : ℝ) (h : Fin d → ℝ) :
    (clippingIdentityHidden^[4]) (clippingFirstHidden j b h) = clippingFirstHidden j b h := by
  apply Function.iterate_fixed
  apply clipping_identity_hidden_fixed
  intro r
  exact le_max_left _ _

noncomputable def clippingOutputMatrix {d : ℕ} (j : Fin d) : Matrix (Fin d) (Fin 4) ℝ :=
  fun r k => if r=j then ![1,-1,-1,1] k else 0

noncomputable def clippingOutputBias {d : ℕ} (j : Fin d) (b : ℝ) : Fin d → ℝ :=
  fun r => if r=j then -b else 0

/- One affine/ReLU input layer, four affine/ReLU identity hidden layers,
   and one affine output layer: six affine layers with hidden width four. -/
noncomputable def sixLayerClippingFFN {d : ℕ} (j : Fin d) (b : ℝ) (h : Fin d → ℝ) : Fin d → ℝ :=
  fun r => (clippingOutputMatrix j).mulVec
    ((clippingIdentityHidden^[4]) (clippingFirstHidden j b h)) r+clippingOutputBias j b r

theorem six_layer_clipping_correction {d : ℕ} (j : Fin d) (b : ℝ) (h : Fin d → ℝ) :
    sixLayerClippingFFN j b h j = clippingCorrection b (h j) := by
  unfold sixLayerClippingFFN
  rw [clipping_hidden_padding_exact]
  simp only [Matrix.mulVec, dotProduct, clippingOutputMatrix, clippingOutputBias,
    ite_true, Fin.sum_univ_succ]
  simp only [clippingFirstHidden, clipping_input_matrix_action, clippingInputBias,
    clippingCorrection]
  simp
  ring

theorem six_layer_clipping_other_rows {d : ℕ} (j r : Fin d) (hr : r ≠ j)
    (b : ℝ) (h : Fin d → ℝ) : sixLayerClippingFFN j b h r = 0 := by
  simp [sixLayerClippingFFN, clippingOutputMatrix, clippingOutputBias, Matrix.mulVec, dotProduct, hr]

theorem six_layer_residual_clipping {d : ℕ} (j : Fin d) (b : ℝ) (hb : 0 ≤ b) (h : Fin d → ℝ) :
    h j+sixLayerClippingFFN j b h j = max (-b) (min (h j) b) := by
  rw [six_layer_clipping_correction]
  exact clipping_residual b (h j) hb

theorem six_layer_hidden_width_fits (D : ℕ) : 4 ≤ 2*D+6 := by omega

#print axioms clipping_input_matrix_action
#print axioms clipping_identity_hidden_fixed
#print axioms clipping_hidden_padding_exact
#print axioms six_layer_clipping_correction
#print axioms six_layer_clipping_other_rows
#print axioms six_layer_residual_clipping
#print axioms six_layer_hidden_width_fits
end GeneralizationCheck
