module

public import ICLGeneralization.PositionalSelection
public import Mathlib.Data.Matrix.Mul

@[expose] public section

open Matrix
namespace GeneralizationCheck

def cosineRow (m : ℕ) : Fin (m+3) := ⟨m, by omega⟩
def sineRow (m : ℕ) : Fin (m+3) := ⟨m+1, by omega⟩
def constantRow (m : ℕ) : Fin (m+3) := ⟨m+2, by omega⟩

noncomputable def readRow {d : ℕ} (r : Fin d) (c : Fin d) : ℝ := if c=r then 1 else 0

theorem read_row_action {d : ℕ} (r : Fin d) (h : Fin d → ℝ) :
    (∑ c, readRow r c*h c) = h r := by
  classical
  simp [readRow]

theorem combined_row_action {d : ℕ} (r s : Fin d) (a b : ℝ) (h : Fin d → ℝ) :
    (∑ c, (a*readRow r c+b*readRow s c)*h c) = a*h r+b*h s := by
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    read_row_action, read_row_action]

noncomputable def extendedQuery (m ℓ : ℕ) (C : ℝ) (target : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) : Matrix (Fin (m+3)) (Fin (m+3)) ℝ :=
  fun r c => Fin.addCases (fun p => A p c)
    (fun p => ![C*Real.cos (tokenAngle ℓ target)*readRow (cosineRow m) c+
                C*Real.sin (tokenAngle ℓ target)*readRow (sineRow m) c,
               0, readRow (constantRow m) c] p) r

noncomputable def extendedKey (m ℓ : ℕ) (C : ℝ) (source : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) : Matrix (Fin (m+3)) (Fin (m+3)) ℝ :=
  fun r c => Fin.addCases (fun p => A p c)
    (fun p => ![Real.cos (tokenAngle ℓ source)*readRow (cosineRow m) c+
                Real.sin (tokenAngle ℓ source)*readRow (sineRow m) c,
               0, -C*readRow (constantRow m) c] p) r

theorem extended_query_data (m ℓ : ℕ) (C : ℝ) (target : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (h : Fin (m+3) → ℝ) (r : Fin m) :
    (extendedQuery m ℓ C target A).mulVec h (r.castAdd 3) = A.mulVec h r := by
  simp [Matrix.mulVec, dotProduct, extendedQuery]

theorem extended_key_data (m ℓ : ℕ) (C : ℝ) (source : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (h : Fin (m+3) → ℝ) (r : Fin m) :
    (extendedKey m ℓ C source A).mulVec h (r.castAdd 3) = A.mulVec h r := by
  simp [Matrix.mulVec, dotProduct, extendedKey]

theorem extended_query_position (m ℓ : ℕ) (C : ℝ) (target q : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (h : Fin (m+3) → ℝ)
    (hcos : h (cosineRow m)=Real.cos (tokenAngle ℓ q))
    (hsin : h (sineRow m)=Real.sin (tokenAngle ℓ q))
    (hone : h (constantRow m)=1) (r : Fin 3) :
    (extendedQuery m ℓ C target A).mulVec h (Fin.natAdd m r) =
      positionalQuery ℓ C target q r := by
  fin_cases r
  · simp only [Matrix.mulVec, dotProduct, extendedQuery, Fin.addCases_right]
    change (∑ c, (C*Real.cos (tokenAngle ℓ target)*readRow (cosineRow m) c+
      C*Real.sin (tokenAngle ℓ target)*readRow (sineRow m) c)*h c) =
      C*(Real.cos (tokenAngle ℓ target)*Real.cos (tokenAngle ℓ q)+
        Real.sin (tokenAngle ℓ target)*Real.sin (tokenAngle ℓ q))
    rw [combined_row_action, hcos, hsin]
    ring
  · simp [Matrix.mulVec, dotProduct, extendedQuery, positionalQuery]
  · simp only [Matrix.mulVec, dotProduct, extendedQuery, Fin.addCases_right]
    change (∑ c, readRow (constantRow m) c*h c)=1
    rw [read_row_action, hone]

theorem extended_key_position (m ℓ : ℕ) (C : ℝ) (source k : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (h : Fin (m+3) → ℝ)
    (hcos : h (cosineRow m)=Real.cos (tokenAngle ℓ k))
    (hsin : h (sineRow m)=Real.sin (tokenAngle ℓ k))
    (hone : h (constantRow m)=1) (r : Fin 3) :
    (extendedKey m ℓ C source A).mulVec h (Fin.natAdd m r) =
      positionalKey ℓ C source k r := by
  fin_cases r
  · simp only [Matrix.mulVec, dotProduct, extendedKey, Fin.addCases_right]
    change (∑ c, (Real.cos (tokenAngle ℓ source)*readRow (cosineRow m) c+
      Real.sin (tokenAngle ℓ source)*readRow (sineRow m) c)*h c) =
      Real.cos (tokenAngle ℓ source)*Real.cos (tokenAngle ℓ k)+
        Real.sin (tokenAngle ℓ source)*Real.sin (tokenAngle ℓ k)
    rw [combined_row_action, hcos, hsin]
  · simp [Matrix.mulVec, dotProduct, extendedKey, positionalKey]
  · simp only [Matrix.mulVec, dotProduct, extendedKey, Fin.addCases_right]
    change (∑ c, (-C*readRow (constantRow m) c)*h c) = -C
    simp only [mul_assoc]
    rw [← Finset.mul_sum, read_row_action, hone]
    ring

theorem extended_matrix_score (m ℓ : ℕ) (C : ℝ) (target source q k : Fin ℓ)
    (Q K : Matrix (Fin m) (Fin (m+3)) ℝ) (H : Fin ℓ → Fin (m+3) → ℝ)
    (hcos : ∀ t, H t (cosineRow m)=Real.cos (tokenAngle ℓ t))
    (hsin : ∀ t, H t (sineRow m)=Real.sin (tokenAngle ℓ t))
    (hone : ∀ t, H t (constantRow m)=1) :
    (∑ r, (extendedQuery m ℓ C target Q).mulVec (H q) r *
      (extendedKey m ℓ C source K).mulVec (H k) r) =
    (∑ r, Q.mulVec (H q) r*K.mulVec (H k) r)+positionalPenalty ℓ C target source q k := by
  rw [Fin.sum_univ_add]
  simp_rw [extended_query_data, extended_key_data,
    extended_query_position m ℓ C target q Q (H q) (hcos q) (hsin q) (hone q),
    extended_key_position m ℓ C source k K (H k) (hcos k) (hsin k) (hone k)]
  rw [positional_query_key_dot]

theorem matrix_attention_selection (m ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (target source : Fin ℓ) (Q K : Matrix (Fin m) (Fin (m+3)) ℝ)
    (V : Matrix (Fin (m+3)) (Fin (m+3)) ℝ) (H : Fin ℓ → Fin (m+3) → ℝ)
    (hcos : ∀ t, H t (cosineRow m)=Real.cos (tokenAngle ℓ t))
    (hsin : ∀ t, H t (sineRow m)=Real.sin (tokenAngle ℓ t))
    (hone : ∀ t, H t (constantRow m)=1)
    (hscore : ∀ q k, (∑ r, Q.mulVec (H q) r*K.mulVec (H k) r) ≤ B)
    (q : Fin ℓ) (r : Fin (m+3)) :
    (∑ k, max 0 (∑ p,
      (extendedQuery m ℓ (2*B*(ℓ : ℝ)^2) target Q).mulVec (H q) p *
      (extendedKey m ℓ (2*B*(ℓ : ℝ)^2) source K).mulVec (H k) p)*V.mulVec (H k) r) =
    if q=target then max 0 (∑ p, Q.mulVec (H q) p*K.mulVec (H source) p)*
      V.mulVec (H source) r else 0 := by
  simp_rw [extended_matrix_score m ℓ _ target source _ _ Q K H hcos hsin hone]
  exact relu_head_selection ℓ B hB target source
    (fun q k => ∑ p, Q.mulVec (H q) p*K.mulVec (H k) p) hscore
    (fun k => V.mulVec (H k) r) q

theorem read_row_abs_bound {d : ℕ} (r c : Fin d) : |readRow r c| ≤ 1 := by
  unfold readRow
  split_ifs <;> norm_num

theorem positional_scaled_coefficient_bound {d : ℕ} (r c : Fin d) (C θ : ℝ) (hC : 0 ≤ C) :
    |C*Real.cos θ*readRow r c| ≤ C := by
  rw [abs_mul, abs_mul, abs_of_nonneg hC]
  calc
    _ ≤ C*1*1 := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) hC)
      (read_row_abs_bound r c) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem positional_scaled_sine_coefficient_bound {d : ℕ} (r c : Fin d) (C θ : ℝ) (hC : 0 ≤ C) :
    |C*Real.sin θ*readRow r c| ≤ C := by
  rw [abs_mul, abs_mul, abs_of_nonneg hC]
  calc
    _ ≤ C*1*1 := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hC)
      (read_row_abs_bound r c) (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem extended_query_coefficient_bound (m ℓ : ℕ) (C κ : ℝ) (hC : 0 ≤ C) (target : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (hA : ∀ r c, |A r c| ≤ κ)
    (r c : Fin (m+3)) : |extendedQuery m ℓ C target A r c| ≤ max κ (2*C+2) := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) r
  · simp only [extendedQuery, Fin.addCases_left]
    exact (hA p c).trans (le_max_left _ _)
  · simp only [extendedQuery, Fin.addCases_right]
    fin_cases p
    · change |C*Real.cos (tokenAngle ℓ target)*readRow (cosineRow m) c+
        C*Real.sin (tokenAngle ℓ target)*readRow (sineRow m) c| ≤ _
      calc
        _ ≤ |C*Real.cos (tokenAngle ℓ target)*readRow (cosineRow m) c|+
            |C*Real.sin (tokenAngle ℓ target)*readRow (sineRow m) c| := abs_add_le _ _
        _ ≤ C+C := add_le_add (positional_scaled_coefficient_bound _ _ C _ hC)
          (positional_scaled_sine_coefficient_bound _ _ C _ hC)
        _ ≤ max κ (2*C+2) := (by linarith : C+C ≤ 2*C+2).trans (le_max_right _ _)
    · change |(0 : ℝ)| ≤ _
      exact (by norm_num; linarith : |(0 : ℝ)| ≤ 2*C+2).trans (le_max_right _ _)
    · change |readRow (constantRow m) c| ≤ _
      exact (read_row_abs_bound _ _).trans
        ((by linarith : (1 : ℝ) ≤ 2*C+2).trans (le_max_right _ _))

theorem extended_key_coefficient_bound (m ℓ : ℕ) (C κ : ℝ) (hC : 0 ≤ C) (source : Fin ℓ)
    (A : Matrix (Fin m) (Fin (m+3)) ℝ) (hA : ∀ r c, |A r c| ≤ κ)
    (r c : Fin (m+3)) : |extendedKey m ℓ C source A r c| ≤ max κ (2*C+2) := by
  refine Fin.addCases (fun p => ?_) (fun p => ?_) r
  · simp only [extendedKey, Fin.addCases_left]
    exact (hA p c).trans (le_max_left _ _)
  · simp only [extendedKey, Fin.addCases_right]
    fin_cases p
    · change |Real.cos (tokenAngle ℓ source)*readRow (cosineRow m) c+
        Real.sin (tokenAngle ℓ source)*readRow (sineRow m) c| ≤ _
      have hc : |Real.cos (tokenAngle ℓ source)*readRow (cosineRow m) c| ≤ 1 := by
        simpa using positional_scaled_coefficient_bound (cosineRow m) c 1 _ (by norm_num)
      have hs : |Real.sin (tokenAngle ℓ source)*readRow (sineRow m) c| ≤ 1 := by
        simpa using positional_scaled_sine_coefficient_bound (sineRow m) c 1 _ (by norm_num)
      exact (abs_add_le _ _).trans ((add_le_add hc hs).trans
        ((by linarith : (1 : ℝ)+1 ≤ 2*C+2).trans (le_max_right _ _)))
    · change |(0 : ℝ)| ≤ _
      exact (by norm_num; linarith : |(0 : ℝ)| ≤ 2*C+2).trans (le_max_right _ _)
    · change |-C*readRow (constantRow m) c| ≤ _
      rw [abs_mul, abs_neg, abs_of_nonneg hC]
      have h := mul_le_mul_of_nonneg_left (read_row_abs_bound (constantRow m) c) hC
      exact h.trans ((by linarith : C*1 ≤ 2*C+2).trans (le_max_right _ _))

#print axioms read_row_action
#print axioms combined_row_action
#print axioms extended_query_data
#print axioms extended_key_data
#print axioms extended_query_position
#print axioms extended_key_position
#print axioms extended_matrix_score
#print axioms matrix_attention_selection
#print axioms read_row_abs_bound
#print axioms positional_scaled_coefficient_bound
#print axioms positional_scaled_sine_coefficient_bound
#print axioms extended_query_coefficient_bound
#print axioms extended_key_coefficient_bound
end GeneralizationCheck
