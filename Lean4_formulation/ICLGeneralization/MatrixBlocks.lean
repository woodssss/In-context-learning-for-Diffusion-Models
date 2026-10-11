module

public import ICLGeneralization.FlatEmbedding
public import ICLGeneralization.DistanceFeatures

@[expose] public section

open Matrix
namespace GeneralizationCheck

noncomputable def writeRows (D : ℕ) (v : Fin (embedWidth D) → ℝ)
    (w : Fin D → Fin (embedWidth D) → ℝ) (l : Fin (embedWidth D) → ℝ) :
    Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ :=
  fun r c => Fin.addCases
    (Fin.addCases (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => v c))
      (Fin.addCases (fun i => w i c) (fun p : Fin 2 => ![l c,0] p)))
    (fun _ : Fin 3 => 0) r

noncomputable def copyValueMatrix (D : ℕ) (j : Fin D) :=
  writeRows D (readRow (cleanFlat j)) (fun _ _ => 0) (fun _ => 0)
noncomputable def differenceValueMatrix (D : ℕ) (a : ℝ) :=
  writeRows D (fun _ => 0) (fun i c => a*readRow (cleanFlat i) c) (fun _ => 0)
noncomputable def logitValueMatrix (D : ℕ) :=
  writeRows D (fun _ => 0) (fun _ _ => 0) (readRow (constantRow (coreWidth D)))

noncomputable def matrixBlockOne (n D : ℕ) (j : Fin D)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  fun q r => H q r+∑ i : Fin n, selectedMatrixHead n D 1 i.castSucc i.castSucc
    (constantData D) (constantData D) (copyValueMatrix D j) H q r

noncomputable def matrixBlockTwo (n D : ℕ) (a : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  fun q r => H q r+∑ i : Fin n, selectedMatrixHead n D 1 i.castSucc i.castSucc
    (constantData D) (constantData D) (differenceValueMatrix D (-a)) H q r

noncomputable def matrixBlockThree (n D : ℕ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  fun q r => H q r+∑ i : Fin n, selectedMatrixHead n D 1 i.castSucc (Fin.last n)
    (constantData D) (constantData D) (differenceValueMatrix D 1) H q r

theorem write_rows_action (D : ℕ) (v : Fin (embedWidth D) → ℝ)
    (w : Fin D → Fin (embedWidth D) → ℝ) (l h : Fin (embedWidth D) → ℝ) :
    (writeRows D v w l).mulVec h =
    Fin.addCases
      (Fin.addCases (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => ∑ c, v c*h c))
        (Fin.addCases (fun i => ∑ c, w i c*h c) (fun p : Fin 2 => ![∑ c, l c*h c,0] p)))
      (fun _ : Fin 3 => 0) := by
  funext r
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [writeRows, Matrix.mulVec, dotProduct]
      · simp [writeRows, Matrix.mulVec, dotProduct]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [writeRows, Matrix.mulVec, dotProduct]
      · fin_cases r <;> simp [writeRows, Matrix.mulVec, dotProduct]
  · simp [writeRows, Matrix.mulVec, dotProduct]

theorem matrix_block_one_state {n D : ℕ} (j : Fin D) (H : RealizationState n D) :
    matrixBlockOne n D j (packState H) = packState (blockOne n D j H) := by
  funext q r
  simp only [matrixBlockOne, selected_matrix_head_state, constant_data_score]
  simp only [copyValueMatrix, write_rows_action]
  simp_rw [read_row_action, pack_clean]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockOne, reluHead]
      · simp [packState, packCore, blockOne, copyHead, reluHead]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockOne, reluHead]
      · fin_cases r <;> simp [packState, packCore, blockOne, reluHead]
  · simp [packState, blockOne, reluHead]

theorem matrix_block_two_state {n D : ℕ} (a : ℝ) (H : RealizationState n D) :
    matrixBlockTwo n D a (packState H) = packState (blockTwo n D a H) := by
  funext q r
  simp only [matrixBlockTwo, selected_matrix_head_state, constant_data_score]
  simp only [differenceValueMatrix, write_rows_action]
  simp_rw [mul_assoc, ← Finset.mul_sum, read_row_action, pack_clean]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockTwo, reluHead]
      · simp [packState, packCore, blockTwo, reluHead]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockTwo, copyHead, reluHead]
      · fin_cases r <;> simp [packState, packCore, blockTwo, reluHead]
  · simp [packState, blockTwo, reluHead]

theorem matrix_block_three_state {n D : ℕ} (H : RealizationState n D) :
    matrixBlockThree n D (packState H) = packState (blockThree n D H) := by
  funext q r
  simp only [matrixBlockThree, selected_matrix_head_state, constant_data_score]
  simp only [differenceValueMatrix, write_rows_action]
  simp_rw [one_mul, read_row_action, pack_clean]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockThree, reluHead]
      · simp [packState, packCore, blockThree, reluHead]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockThree, copyHead, reluHead]
      · fin_cases r <;> simp [packState, packCore, blockThree, reluHead]
  · simp [packState, blockThree, reluHead]

noncomputable def distanceData (D : ℕ) (M s sign : ℝ) :
    Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ :=
  fun r c => Fin.addCases (fun _ => 0)
    (Fin.addCases (fun i => sign/(Real.sqrt 2*s)*readRow (differenceFlat i) c)
      (fun p : Fin 2 => ![Real.sqrt M*readRow (constantRow (coreWidth D)) c,0] p)) r

theorem distance_data_action {n D : ℕ} (M s sign : ℝ) (H : RealizationState n D)
    (q : Fin (n+1)) :
    (distanceData D M s sign).mulVec (packState H q) =
    Fin.addCases (fun _ : Fin (D+1) => 0)
      (Fin.addCases (fun i => sign/(Real.sqrt 2*s)*H.difference q i)
        (fun p : Fin 2 => ![Real.sqrt M,0] p)) := by
  funext r
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simp [distanceData, Matrix.mulVec, dotProduct]
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simp only [distanceData, Matrix.mulVec, dotProduct, Fin.addCases_right,
        Fin.addCases_left, mul_assoc, ← Finset.mul_sum, read_row_action, pack_difference]
    · fin_cases r
      · simp only [distanceData, Matrix.mulVec, dotProduct, Fin.addCases_right]
        change (∑ c, (Real.sqrt M*readRow (constantRow (coreWidth D)) c)*packState H q c) = _
        simp only [mul_assoc, ← Finset.mul_sum, read_row_action, pack_constant, mul_one]
        rfl
      · simp [distanceData, Matrix.mulVec, dotProduct]

theorem distance_data_score {n D : ℕ} (M s : ℝ) (hM : 0 ≤ M) (hs : s ≠ 0)
    (H : RealizationState n D) (q k : Fin (n+1)) :
    (∑ r, (distanceData D M s 1).mulVec (packState H q) r*
      (distanceData D M s (-1)).mulVec (packState H k) r) = distanceScore n D M s H q k := by
  simp only [distance_data_action]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
  have h := distance_feature_dot D M s 1 1 hM hs (H.difference q) (H.difference k)
  simp only [distanceQueryFeatures, distanceKeyFeatures, Fin.sum_univ_add,
    Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_one, mul_one] at h
  convert h using 1 <;> simp [distanceScore, div_mul_eq_mul_div, neg_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

noncomputable def matrixBlockFour (n D : ℕ) (M s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :=
  fun q r => H q r+∑ i : Fin n, selectedMatrixHead n D (2*M) i.castSucc i.castSucc
    (distanceData D M s 1) (distanceData D M s (-1)) (logitValueMatrix D) H q r

theorem matrix_block_four_state {n D : ℕ} (M s : ℝ) (hM : 0 ≤ M) (hs : s ≠ 0)
    (H : RealizationState n D) :
    matrixBlockFour n D M s (packState H) = packState (blockFour n D M s H) := by
  funext q r
  simp only [matrixBlockFour, selected_matrix_head_state, distance_data_score M s hM hs]
  simp only [logitValueMatrix, write_rows_action]
  simp_rw [read_row_action, pack_constant]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockFour, reluHead]
      · simp [packState, packCore, blockFour, reluHead]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [packState, packCore, blockFour, reluHead]
      · fin_cases r <;> simp [packState, packCore, blockFour, reluHead]
  · simp [packState, blockFour, reluHead]

#print axioms write_rows_action
#print axioms matrix_block_one_state
#print axioms matrix_block_two_state
#print axioms matrix_block_three_state
#print axioms distance_data_action
#print axioms distance_data_score
#print axioms matrix_block_four_state
end GeneralizationCheck
