module

public import ICLGeneralization.TransformerNetwork

@[expose] public section

open Matrix
namespace GeneralizationCheck

def MatrixBound {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ) (κ : ℝ) : Prop :=
  ∀ r c, |A r c| ≤ κ

def ScheduledMatrix.Bounded {d : ℕ} (A : ScheduledMatrix d) (κ : ℝ) : Prop :=
  MatrixBound A.base κ ∧ MatrixBound A.alpha κ ∧ MatrixBound A.reciprocal κ

def ScheduledHead.Bounded {d : ℕ} (A : ScheduledHead d) (κ : ℝ) : Prop :=
  A.query.Bounded κ ∧ A.key.Bounded κ ∧ A.value.Bounded κ

def FiveBlockTransformer.Bounded {n D : ℕ} (T : FiveBlockTransformer n D) (κ : ℝ) : Prop :=
  (∀ k i, (T.reluHeads k i).Bounded κ) ∧ (∀ k, (T.reluFFN k).Bounded κ) ∧
  T.finalHead.Bounded κ ∧ T.finalFFN.Bounded κ

theorem matrix_bound_mono {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ) (κ κnext : ℝ)
    (hA : MatrixBound A κ) (h : κ ≤ κnext) : MatrixBound A κnext := fun r c => (hA r c).trans h

theorem zero_matrix_bound (d e : ℕ) (κ : ℝ) (hκ : 0 ≤ κ) :
    MatrixBound (0 : Matrix (Fin d) (Fin e) ℝ) κ := by
  intro r c
  simpa using hκ

theorem fixed_matrix_bounded {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hA : MatrixBound A κ) : (fixedMatrix A).Bounded κ :=
  ⟨hA, zero_matrix_bound d d κ hκ, zero_matrix_bound d d κ hκ⟩

theorem alpha_matrix_bounded {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (κ : ℝ)
    (hκ : 0 ≤ κ) (hA : MatrixBound A κ) : (alphaMatrix A).Bounded κ :=
  ⟨zero_matrix_bound d d κ hκ, hA, zero_matrix_bound d d κ hκ⟩

theorem constant_data_bound (D : ℕ) : MatrixBound (constantData D) 1 := by
  intro r c
  unfold constantData
  split_ifs
  · exact read_row_abs_bound _ _
  · norm_num

theorem write_rows_bound (D : ℕ) (v : Fin (embedWidth D) → ℝ)
    (w : Fin D → Fin (embedWidth D) → ℝ) (l : Fin (embedWidth D) → ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hv : ∀ c, |v c| ≤ κ)
    (hw : ∀ i c, |w i c| ≤ κ) (hl : ∀ c, |l c| ≤ κ) :
    MatrixBound (writeRows D v w l) κ := by
  intro r c
  have hzero : |(0 : ℝ)| ≤ κ := by simpa using hκ
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simpa only [writeRows, Fin.addCases_left] using hzero
      · simpa only [writeRows, Fin.addCases_left, Fin.addCases_right] using hv c
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simpa only [writeRows, Fin.addCases_left, Fin.addCases_right] using hw r c
      · fin_cases r
        · simpa [writeRows] using hl c
        · simpa [writeRows] using hzero
  · simpa only [writeRows, Fin.addCases_right] using hzero

theorem copy_value_matrix_bound (D : ℕ) (j : Fin D) : MatrixBound (copyValueMatrix D j) 1 := by
  apply write_rows_bound D _ _ _ 1 (by norm_num)
  · exact read_row_abs_bound _
  · intros; norm_num
  · intros; norm_num

theorem difference_value_matrix_bound (D : ℕ) (a : ℝ) (ha : |a| ≤ 1) :
    MatrixBound (differenceValueMatrix D a) 1 := by
  apply write_rows_bound D _ _ _ 1 (by norm_num)
  · intros; norm_num
  · intro i c
    rw [abs_mul]
    exact (mul_le_mul ha (read_row_abs_bound _ _) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  · intros; norm_num

theorem logit_value_matrix_bound (D : ℕ) : MatrixBound (logitValueMatrix D) 1 := by
  apply write_rows_bound D _ _ _ 1 (by norm_num)
  · intros; norm_num
  · intros; norm_num
  · exact read_row_abs_bound _

theorem rank_one_read_bound {d : ℕ} (out source : Fin d) : MatrixBound (rankOneRead out source) 1 := by
  intro r c
  rw [rankOneRead, abs_mul]
  exact (mul_le_mul (read_row_abs_bound _ _) (read_row_abs_bound _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem reciprocal_root_two_bound : |1/Real.sqrt 2| ≤ 1 := by
  have h : 1 ≤ Real.sqrt 2 := by norm_num
  rw [abs_of_nonneg (by positivity : 0 ≤ 1/Real.sqrt 2)]
  exact (div_le_one (by positivity : 0 < Real.sqrt 2)).2 h

theorem distance_data_basis_bound (D : ℕ) (N sign κ : ℝ) (hκ : 1 ≤ κ)
    (hroot : |Real.sqrt N| ≤ κ) (hsign : |sign| ≤ 1) :
    MatrixBound (distanceData D N 1 sign) κ := by
  intro r c
  have hzero : |(0 : ℝ)| ≤ κ := by norm_num; linarith
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simpa [distanceData] using hzero
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simp only [distanceData, Fin.addCases_right, Fin.addCases_left, mul_one, abs_mul]
      have hcoef : |sign/Real.sqrt 2| ≤ 1 := by
        rw [div_eq_mul_inv, abs_mul]
        simpa only [one_div, one_mul] using
          mul_le_mul hsign reciprocal_root_two_bound (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      exact ((mul_le_mul hcoef (read_row_abs_bound _ _) (abs_nonneg _)
        (by norm_num)).trans_eq (by ring)).trans hκ
    · fin_cases r
      · simp only [distanceData, Fin.addCases_right]
        change |Real.sqrt N*readRow (constantRow (coreWidth D)) c| ≤ κ
        rw [abs_mul]
        exact (mul_le_mul hroot (read_row_abs_bound _ _) (abs_nonneg _) (by linarith : 0 ≤ κ)).trans_eq
          (by ring)
      · simpa [distanceData] using hzero

theorem lift_data_bound (D : ℕ) (A : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ)
    (κ : ℝ) (hκ : 0 ≤ κ) (hA : MatrixBound A κ) : MatrixBound (liftData D A) κ := by
  intro r c
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simpa only [liftData, Fin.addCases_left] using hA r c
  · simpa only [liftData, Fin.addCases_right, abs_zero] using hκ

noncomputable def intermediateBudget (n : ℕ) (M : ℝ) := 10*(n+1 : ℝ)^2*M

theorem intermediate_budget_dominates (n : ℕ) (M : ℝ) (hM : 1 ≤ M) :
    M ≤ intermediateBudget n M := by
  have hn : 1 ≤ (n+1 : ℝ) := by have h := Nat.cast_nonneg (α := ℝ) n; linarith
  have hsq : 1 ≤ (n+1 : ℝ)^2 := by nlinarith
  have h := mul_le_mul_of_nonneg_right hsq (by linarith : 0 ≤ M)
  unfold intermediateBudget
  nlinarith

theorem extended_selection_budget (n D : ℕ) (M C : ℝ) (hM : 1 ≤ M) (hC : 0 ≤ C)
    (hCmax : C ≤ 4*M*(n+1 : ℝ)^2) (i : Fin (n+1))
    (A : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ) (hA : MatrixBound A M) :
    MatrixBound (extendedQuery (coreWidth D) (n+1) C i A) (intermediateBudget n M) ∧
    MatrixBound (extendedKey (coreWidth D) (n+1) C i A) (intermediateBudget n M) := by
  have hp : 2*C+2 ≤ intermediateBudget n M := by
    have h := selector_coefficient_budget (n+1) (by omega) M hM
    simp only [Nat.cast_add, Nat.cast_one] at h
    unfold intermediateBudget
    linarith
  have hm : max M (2*C+2) ≤ intermediateBudget n M :=
    max_le (intermediate_budget_dominates n M hM) hp
  constructor <;> intro r c
  · exact (extended_query_coefficient_bound _ _ C M hC i A hA r c).trans hm
  · exact (extended_key_coefficient_bound _ _ C M hC i A hA r c).trans hm

theorem scheduled_distance_bounded (n D : ℕ) (M : ℝ) (hM : 1 ≤ M) (i : Fin (n+1)) :
    (scheduledDistanceQuery n D M i).Bounded (intermediateBudget n M) ∧
    (scheduledDistanceKey n D M i).Bounded (intermediateBudget n M) := by
  have hM0 : 0 ≤ M := by linarith
  have hm := intermediate_budget_dominates n M hM
  have hk : 0 ≤ intermediateBudget n M := hM0.trans hm
  have hbase := distance_data_basis_bound D M 0 M hM (distance_constant_coefficient_bound M hM)
    (by norm_num)
  have hex := extended_selection_budget n D M (4*M*(n+1 : ℝ)^2) hM (by positivity)
    (le_refl _) i _ hbase
  have hrec (sign : ℝ) (hsign : |sign| ≤ 1) :
      MatrixBound (liftData D (distanceData D 0 1 sign)) (intermediateBudget n M) :=
    matrix_bound_mono _ M _ (lift_data_bound D _ M hM0
      (distance_data_basis_bound D 0 sign M hM (by simpa using hM0) hsign)) hm
  exact ⟨⟨hex.1, zero_matrix_bound _ _ _ hk, hrec 1 (by norm_num)⟩,
    ⟨hex.2, zero_matrix_bound _ _ _ hk, hrec (-1) (by norm_num)⟩⟩

theorem copy_scheduled_head_bounded (n D : ℕ) (M : ℝ) (hM : 1 ≤ M)
    (target source : Fin (n+1)) (V : ScheduledMatrix (embedWidth D))
    (hV : V.Bounded (intermediateBudget n M)) :
    (copyScheduledHead n D target source V).Bounded (intermediateBudget n M) := by
  have hm := intermediate_budget_dominates n M hM
  have hk : 0 ≤ intermediateBudget n M := (by linarith : 0 ≤ M).trans hm
  have hA := matrix_bound_mono _ 1 M (constant_data_bound D) hM
  have hC : 2*(n+1 : ℝ)^2 ≤ 4*M*(n+1 : ℝ)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ M-1 by linarith) (sq_nonneg (n+1 : ℝ))]
  exact ⟨fixed_matrix_bounded _ _ hk
      (extended_selection_budget n D M _ hM (by positivity) hC target _ hA).1,
    fixed_matrix_bounded _ _ hk
      (extended_selection_budget n D M _ hM (by positivity) hC source _ hA).2, hV⟩

theorem kernel_transformer_bounded (n D : ℕ) (j : Fin D) (M b : ℝ)
    (hM : 1 ≤ M) (hb : |b| ≤ M) :
    (kernelTransformer n D j M b).Bounded (intermediateBudget n M) := by
  have hm := intermediate_budget_dominates n M hM
  have h1 : 1 ≤ intermediateBudget n M := hM.trans hm
  have hk : 0 ≤ intermediateBudget n M := by linarith
  have mono (A : Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ)
      (hA : MatrixBound A 1) : MatrixBound A (intermediateBudget n M) :=
    matrix_bound_mono A 1 _ hA h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k i
    fin_cases k
    · exact copy_scheduled_head_bounded n D M hM _ _ _
        (fixed_matrix_bounded _ _ hk (mono _ (copy_value_matrix_bound D j)))
    · exact copy_scheduled_head_bounded n D M hM _ _ _
        (alpha_matrix_bounded _ _ hk (mono _ (difference_value_matrix_bound D (-1) (by norm_num))))
    · exact copy_scheduled_head_bounded n D M hM _ _ _
        (fixed_matrix_bounded _ _ hk (mono _ (difference_value_matrix_bound D 1 (by norm_num))))
    · have h := scheduled_distance_bounded n D M hM i.castSucc
      exact ⟨h.1, h.2, fixed_matrix_bounded _ _ hk (mono _ (logit_value_matrix_bound D))⟩
  · intro k
    exact zero_six_ffn_bounded _ _ _ hk
  · exact ⟨fixed_matrix_bounded _ _ hk (mono _ (rank_one_read_bound _ _)),
      fixed_matrix_bounded _ _ hk (mono _ (rank_one_read_bound _ _)),
      fixed_matrix_bounded _ _ hk (mono _ (rank_one_read_bound _ _))⟩
  · exact padded_clipping_ffn_bounded _ _ b _ h1 (hb.trans hm)

theorem network_budget_mono {n D : ℕ} (T : FiveBlockTransformer n D) (κ κnext : ℝ)
    (hT : T.Bounded κ) (h : κ ≤ κnext) : T.Bounded κnext := by
  have hmat {d : ℕ} (A : ScheduledMatrix d) (hA : A.Bounded κ) : A.Bounded κnext :=
    ⟨matrix_bound_mono _ κ κnext hA.1 h, matrix_bound_mono _ κ κnext hA.2.1 h,
      matrix_bound_mono _ κ κnext hA.2.2 h⟩
  have hhead {d : ℕ} (A : ScheduledHead d) (hA : A.Bounded κ) : A.Bounded κnext :=
    ⟨hmat _ hA.1, hmat _ hA.2.1, hmat _ hA.2.2⟩
  have hffn {d w : ℕ} (F : SixLayerFFN d w) (hF : F.Bounded κ) : F.Bounded κnext :=
    ⟨fun r c => (hF.1 r c).trans h, fun r => (hF.2.1 r).trans h,
      fun r c => (hF.2.2.1 r c).trans h, fun r => (hF.2.2.2.1 r).trans h,
      fun r c => (hF.2.2.2.2.1 r c).trans h, fun r => (hF.2.2.2.2.2 r).trans h⟩
  exact ⟨fun k i => hhead _ (hT.1 k i), fun k => hffn _ (hT.2.1 k),
    hhead _ hT.2.2.1, hffn _ hT.2.2.2⟩

#print axioms matrix_bound_mono
#print axioms zero_matrix_bound
#print axioms fixed_matrix_bounded
#print axioms alpha_matrix_bounded
#print axioms constant_data_bound
#print axioms write_rows_bound
#print axioms copy_value_matrix_bound
#print axioms difference_value_matrix_bound
#print axioms logit_value_matrix_bound
#print axioms rank_one_read_bound
#print axioms reciprocal_root_two_bound
#print axioms distance_data_basis_bound
#print axioms lift_data_bound
#print axioms intermediate_budget_dominates
#print axioms extended_selection_budget
#print axioms scheduled_distance_bounded
#print axioms copy_scheduled_head_bounded
#print axioms kernel_transformer_bounded
#print axioms network_budget_mono
end GeneralizationCheck
