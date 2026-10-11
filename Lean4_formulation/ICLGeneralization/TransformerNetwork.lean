module

public import ICLGeneralization.ScheduledMatrices
public import ICLGeneralization.PaddedFFN

@[expose] public section

open Matrix
namespace GeneralizationCheck

structure ScheduledHead (d : ℕ) where
  query : ScheduledMatrix d
  key : ScheduledMatrix d
  value : ScheduledMatrix d

noncomputable def ScheduledHead.relu {d ℓ : ℕ} (A : ScheduledHead d) (a s : ℝ)
    (H : Fin ℓ → Fin d → ℝ) :=
  matrixReLUHead (A.query.eval a s) (A.key.eval a s) (A.value.eval a s) H

noncomputable def ScheduledHead.maskedSoftmax {d n : ℕ} (A : ScheduledHead d) (a s : ℝ)
    (H : Fin (n+1) → Fin d → ℝ) (q : Fin (n+1)) (r : Fin d) : ℝ :=
  softmaxReadout n
    (fun i => ∑ p, (A.query.eval a s).mulVec (H q) p*
      (A.key.eval a s).mulVec (H i.castSucc) p)
    (fun i => (A.value.eval a s).mulVec (H i.castSucc) r)

abbrev hiddenWidth (D : ℕ) := 4+(2*D+2)

/- This type contains four ReLU blocks with n heads each, one final masked
   softmax block with one head, and actual six-affine-layer FFN records.
   Its coefficients do not take a prompt, task, query, or time argument. -/
structure FiveBlockTransformer (n D : ℕ) where
  reluHeads : Fin 4 → Fin n → ScheduledHead (embedWidth D)
  reluFFN : Fin 4 → SixLayerFFN (embedWidth D) (hiddenWidth D)
  finalHead : ScheduledHead (embedWidth D)
  finalFFN : SixLayerFFN (embedWidth D) (hiddenWidth D)

noncomputable def FiveBlockTransformer.reluBlock {n D : ℕ} (T : FiveBlockTransformer n D)
    (k : Fin 4) (a s : ℝ) (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  let Z := fun q r => H q r+∑ i, (T.reluHeads k i).relu a s H q r
  fun q r => Z q r+(T.reluFFN k).eval (Z q) r

noncomputable def FiveBlockTransformer.finalBlock {n D : ℕ} (T : FiveBlockTransformer n D)
    (a s : ℝ) (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  let Z := fun q r => H q r+T.finalHead.maskedSoftmax a s H q r
  fun q r => Z q r+T.finalFFN.eval (Z q) r

noncomputable def FiveBlockTransformer.eval {n D : ℕ} (T : FiveBlockTransformer n D)
    (a s : ℝ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) : ℝ :=
  let H0 := packState (initialState n D x y)
  let H1 := T.reluBlock 0 a s H0
  let H2 := T.reluBlock 1 a s H1
  let H3 := T.reluBlock 2 a s H2
  let H4 := T.reluBlock 3 a s H3
  T.finalBlock a s H4 (Fin.last n) (valueFlat D)

noncomputable def copyScheduledHead (n D : ℕ) (target source : Fin (n+1))
    (V : ScheduledMatrix (embedWidth D)) : ScheduledHead (embedWidth D) where
  query := fixedMatrix (extendedQuery (coreWidth D) (n+1) (2*(n+1 : ℝ)^2) target (constantData D))
  key := fixedMatrix (extendedKey (coreWidth D) (n+1) (2*(n+1 : ℝ)^2) source (constantData D))
  value := V

noncomputable def kernelTransformer (n D : ℕ) (j : Fin D) (M b : ℝ) :
    FiveBlockTransformer n D where
  reluHeads k i := ![
    copyScheduledHead n D i.castSucc i.castSucc (fixedMatrix (copyValueMatrix D j)),
    copyScheduledHead n D i.castSucc i.castSucc (alphaMatrix (differenceValueMatrix D (-1))),
    copyScheduledHead n D i.castSucc (Fin.last n) (fixedMatrix (differenceValueMatrix D 1)),
    { query := scheduledDistanceQuery n D M i.castSucc,
      key := scheduledDistanceKey n D M i.castSucc,
      value := fixedMatrix (logitValueMatrix D) }] k
  reluFFN _ := zeroSixFFN (embedWidth D) (hiddenWidth D)
  finalHead := {
    query := fixedMatrix (rankOneRead (logitFlat D) (constantRow (coreWidth D))),
    key := fixedMatrix (rankOneRead (logitFlat D) (logitFlat D)),
    value := fixedMatrix (rankOneRead (valueFlat D) (valueFlat D)) }
  finalFFN := paddedClippingFFN (2*D+2) (valueFlat D) b

theorem kernel_transformer_relu_zero_ffn (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (k : Fin 4) (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    (kernelTransformer n D j M b).reluBlock k a s H =
    fun q r => H q r+∑ i, ((kernelTransformer n D j M b).reluHeads k i).relu a s H q r := by
  funext q r
  simp [FiveBlockTransformer.reluBlock, kernelTransformer, zero_six_ffn_eval]

theorem kernel_transformer_first_block (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    (kernelTransformer n D j M b).reluBlock 0 a s H = matrixBlockOne n D j H := by
  rw [kernel_transformer_relu_zero_ffn]
  unfold matrixBlockOne selectedMatrixHead
  simp [kernelTransformer, ScheduledHead.relu, copyScheduledHead, fixed_matrix_eval]

theorem kernel_transformer_second_block (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    (kernelTransformer n D j M b).reluBlock 1 a s H = matrixBlockTwo n D a H := by
  rw [kernel_transformer_relu_zero_ffn]
  unfold matrixBlockTwo selectedMatrixHead
  simp [kernelTransformer, ScheduledHead.relu, copyScheduledHead, fixed_matrix_eval,
    difference_value_alpha_eval]

theorem kernel_transformer_third_block (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    (kernelTransformer n D j M b).reluBlock 2 a s H = matrixBlockThree n D H := by
  rw [kernel_transformer_relu_zero_ffn]
  unfold matrixBlockThree selectedMatrixHead
  simp [kernelTransformer, ScheduledHead.relu, copyScheduledHead, fixed_matrix_eval]

theorem kernel_transformer_fourth_block (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    (kernelTransformer n D j M b).reluBlock 3 a s H = matrixBlockFour n D M s H := by
  rw [kernel_transformer_relu_zero_ffn]
  unfold matrixBlockFour selectedMatrixHead
  simp [kernelTransformer, ScheduledHead.relu, scheduled_distance_query_eval,
    scheduled_distance_key_eval, fixed_matrix_eval]

theorem kernel_transformer_final_block {n D : ℕ} (j : Fin D) (M b a s : ℝ)
    (H : RealizationState n D) :
    (kernelTransformer n D j M b).finalBlock a s (packState H) (Fin.last n) (valueFlat D) =
    blockFiveOutput n D b H := by
  classical
  unfold FiveBlockTransformer.finalBlock
  simp only [kernelTransformer, padded_clipping_ffn_eval, six_layer_clipping_correction,
    ScheduledHead.maskedSoftmax, fixed_matrix_eval, rank_one_read_score,
    pack_constant, pack_logit, one_mul]
  simp only [rank_one_read_action, pack_value]
  simp [readRow, blockFiveOutput]

theorem kernel_transformer_evaluation (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (hM : 0 ≤ M) (hs : s ≠ 0) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    (kernelTransformer n D j M b).eval a s x y = constructedOutput n D j a s M b x y := by
  unfold FiveBlockTransformer.eval
  dsimp only
  rw [kernel_transformer_first_block, matrix_block_one_state,
    kernel_transformer_second_block, matrix_block_two_state,
    kernel_transformer_third_block, matrix_block_three_state,
    kernel_transformer_fourth_block, matrix_block_four_state M s hM hs,
    kernel_transformer_final_block]
  rfl

theorem kernel_transformer_exact (n D : ℕ) (hn : 0 < n) (j : Fin D)
    (b R C a s s0 : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1)
    (hs0 : 0 < s0) (hs : s0 ≤ s)
    (x : Fin n → EuclideanSpace ℝ (Fin D)) (z eps : EuclideanSpace ℝ (Fin D))
    (hx : ∀ i r, -b ≤ x i r ∧ x i r ≤ b)
    (hz : ∀ r, -b ≤ z r ∧ z r ≤ b) (heps : ‖eps‖ ≤ C) :
    (kernelTransformer n D j (realizationM D b R s0 C) b).eval a s
      (fun i r => x i r) (fun r => (a • z+s • eps) r) =
    softmaxReadout n
      (fun i => -(∑ r, ((a • z+s • eps) r-a*x i r)^2)/(2*s^2)) (fun i => x i j) := by
  rw [kernel_transformer_evaluation n D j _ b a s (realization_M_nonnegative D b R s0 C)
    (ne_of_gt (lt_of_lt_of_le hs0 hs))]
  exact five_blocks_exact_on_query_region n D hn j b R C a s s0 hb ha hs0 hs x z eps hx hz heps

theorem kernel_transformer_global_bound (n D : ℕ) (j : Fin D) (M b a s : ℝ)
    (hb : 0 ≤ b) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    -b ≤ (kernelTransformer n D j M b).eval a s x y ∧
    (kernelTransformer n D j M b).eval a s x y ≤ b := by
  unfold FiveBlockTransformer.eval FiveBlockTransformer.finalBlock
  simp only [kernelTransformer, padded_clipping_ffn_eval, six_layer_clipping_correction]
  exact clipping_global_bounds b _ hb

theorem network_hidden_dimension (D : ℕ) : hiddenWidth D = 2*D+6 := by
  unfold hiddenWidth
  omega

#print axioms kernel_transformer_relu_zero_ffn
#print axioms kernel_transformer_first_block
#print axioms kernel_transformer_second_block
#print axioms kernel_transformer_third_block
#print axioms kernel_transformer_fourth_block
#print axioms kernel_transformer_final_block
#print axioms kernel_transformer_evaluation
#print axioms kernel_transformer_exact
#print axioms kernel_transformer_global_bound
#print axioms network_hidden_dimension
end GeneralizationCheck
