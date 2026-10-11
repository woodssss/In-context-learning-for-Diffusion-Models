module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Tactic

@[expose] public section

namespace GeneralizationCheck

noncomputable def tokenAngle (ℓ : ℕ) (i : Fin ℓ) : ℝ :=
  ((i : ℝ)+1)*Real.pi/(2*(ℓ : ℝ))

theorem token_angle_difference (ℓ : ℕ) (q i : Fin ℓ) :
    tokenAngle ℓ q-tokenAngle ℓ i = ((q : ℝ)-(i : ℝ))*Real.pi/(2*(ℓ : ℝ)) := by
  unfold tokenAngle
  ring

theorem token_angle_range (ℓ : ℕ) (q i : Fin ℓ) :
    -(Real.pi/2) ≤ tokenAngle ℓ q-tokenAngle ℓ i ∧
    tokenAngle ℓ q-tokenAngle ℓ i ≤ Real.pi/2 := by
  have hℓ : 0 < (ℓ : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt q.isLt)
  have hq : 0 ≤ (q : ℝ) := by positivity
  have hi : 0 ≤ (i : ℝ) := by positivity
  have hql : (q : ℝ) < ℓ := by exact_mod_cast q.isLt
  have hil : (i : ℝ) < ℓ := by exact_mod_cast i.isLt
  rw [token_angle_difference]
  constructor
  · apply (le_div_iff₀ (by positivity : 0 < 2*(ℓ : ℝ))).2
    nlinarith [Real.pi_pos]
  · apply (div_le_iff₀ (by positivity : 0 < 2*(ℓ : ℝ))).2
    nlinarith [Real.pi_pos]

theorem token_cos_nonnegative (ℓ : ℕ) (q i : Fin ℓ) :
    0 ≤ Real.cos (tokenAngle ℓ q-tokenAngle ℓ i) := by
  exact Real.cos_nonneg_of_mem_Icc (token_angle_range ℓ q i)

theorem token_cos_gap (ℓ : ℕ) (q i : Fin ℓ) (hne : q ≠ i) :
    Real.cos (tokenAngle ℓ q-tokenAngle ℓ i) ≤ 1-1/(2*(ℓ : ℝ)^2) := by
  have hℓ : 0 < (ℓ : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt q.isLt)
  have hqi : (q : ℤ) ≠ (i : ℤ) := by
    intro h
    apply hne
    apply Fin.ext
    exact_mod_cast h
  have hd : 1 ≤ |(q : ℝ)-(i : ℝ)| := by
    exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hqi))
  have hsq : 1 ≤ ((q : ℝ)-(i : ℝ))^2 := by
    nlinarith [sq_abs ((q : ℝ)-(i : ℝ))]
  have hr := token_angle_range ℓ q i
  have hcos := Real.cos_le_one_sub_mul_cos_sq
    (show |tokenAngle ℓ q-tokenAngle ℓ i| ≤ Real.pi from
      abs_le.mpr ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  have he : 2/Real.pi^2*(tokenAngle ℓ q-tokenAngle ℓ i)^2 =
      ((q : ℝ)-(i : ℝ))^2/(2*(ℓ : ℝ)^2) := by
    rw [token_angle_difference]
    field_simp
  rw [he] at hcos
  have hg : 1/(2*(ℓ : ℝ)^2) ≤ ((q : ℝ)-(i : ℝ))^2/(2*(ℓ : ℝ)^2) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  linarith

noncomputable def positionalPenalty (ℓ : ℕ) (C : ℝ) (target source q k : Fin ℓ) : ℝ :=
  C*(Real.cos (tokenAngle ℓ q-tokenAngle ℓ target)*
      Real.cos (tokenAngle ℓ k-tokenAngle ℓ source)-1)

theorem positional_penalty_selected (ℓ : ℕ) (C : ℝ) (target source : Fin ℓ) :
    positionalPenalty ℓ C target source target source = 0 := by
  simp [positionalPenalty]

theorem positional_penalty_off_target (ℓ : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (target source q k : Fin ℓ) (hoff : q ≠ target ∨ k ≠ source) :
    positionalPenalty ℓ C target source q k ≤ -C/(2*(ℓ : ℝ)^2) := by
  have hq := token_cos_nonnegative ℓ q target
  have hk := token_cos_nonnegative ℓ k source
  have hq1 := Real.cos_le_one (tokenAngle ℓ q-tokenAngle ℓ target)
  have hk1 := Real.cos_le_one (tokenAngle ℓ k-tokenAngle ℓ source)
  have hp : Real.cos (tokenAngle ℓ q-tokenAngle ℓ target)*
      Real.cos (tokenAngle ℓ k-tokenAngle ℓ source) ≤ 1-1/(2*(ℓ : ℝ)^2) := by
    rcases hoff with h | h
    · exact le_trans (mul_le_of_le_one_right hq hk1) (token_cos_gap ℓ q target h)
    · exact le_trans (mul_le_of_le_one_left hk hq1) (token_cos_gap ℓ k source h)
  unfold positionalPenalty
  have hs : Real.cos (tokenAngle ℓ q-tokenAngle ℓ target)*
      Real.cos (tokenAngle ℓ k-tokenAngle ℓ source)-1 ≤ -1/(2*(ℓ : ℝ)^2) := by
    calc
      _ ≤ (1-1/(2*(ℓ : ℝ)^2))-1 := sub_le_sub_right hp 1
      _ = _ := by ring
  calc
    _ ≤ C*(-1/(2*(ℓ : ℝ)^2)) := mul_le_mul_of_nonneg_left hs hC
    _ = _ := by ring

theorem relu_score_selection (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (target source : Fin ℓ) (score : Fin ℓ → Fin ℓ → ℝ)
    (hscore : ∀ q k, score q k ≤ B) (q k : Fin ℓ) :
    max 0 (score q k+positionalPenalty ℓ (2*B*(ℓ : ℝ)^2) target source q k) =
      if q=target ∧ k=source then max 0 (score q k) else 0 := by
  classical
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    rw [positional_penalty_selected, add_zero]
  · have hoff : q ≠ target ∨ k ≠ source := by tauto
    have hg := positional_penalty_off_target ℓ (2*B*(ℓ : ℝ)^2) (by positivity)
      target source q k hoff
    have hℓ : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt q.isLt)
    have he : -(2*B*(ℓ : ℝ)^2)/(2*(ℓ : ℝ)^2) = -B := by field_simp
    rw [he] at hg
    apply max_eq_left
    calc
      _ ≤ B+(-B) := add_le_add (hscore q k) hg
      _ = 0 := by ring

noncomputable def positionalQuery (ℓ : ℕ) (C : ℝ) (target q : Fin ℓ) : Fin 3 → ℝ :=
  ![C*(Real.cos (tokenAngle ℓ target)*Real.cos (tokenAngle ℓ q)+
       Real.sin (tokenAngle ℓ target)*Real.sin (tokenAngle ℓ q)), 0, 1]

noncomputable def positionalKey (ℓ : ℕ) (C : ℝ) (source k : Fin ℓ) : Fin 3 → ℝ :=
  ![Real.cos (tokenAngle ℓ source)*Real.cos (tokenAngle ℓ k)+
      Real.sin (tokenAngle ℓ source)*Real.sin (tokenAngle ℓ k), 0, -C]

theorem positional_query_key_dot (ℓ : ℕ) (C : ℝ) (target source q k : Fin ℓ) :
    (∑ r : Fin 3, positionalQuery ℓ C target q r * positionalKey ℓ C source k r) =
      positionalPenalty ℓ C target source q k := by
  simp [positionalQuery, positionalKey, positionalPenalty, Fin.sum_univ_succ, Real.cos_sub]
  ring

noncomputable def reluHead (ℓ : ℕ) (B : ℝ) (target source : Fin ℓ)
    (score : Fin ℓ → Fin ℓ → ℝ) (value : Fin ℓ → ℝ) (q : Fin ℓ) : ℝ :=
  ∑ k, max 0 (score q k+positionalPenalty ℓ (2*B*(ℓ : ℝ)^2) target source q k)*value k

theorem relu_head_selection (ℓ : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (target source : Fin ℓ) (score : Fin ℓ → Fin ℓ → ℝ)
    (hscore : ∀ q k, score q k ≤ B) (value : Fin ℓ → ℝ) (q : Fin ℓ) :
    reluHead ℓ B target source score value q =
      if q=target then max 0 (score q source)*value source else 0 := by
  classical
  unfold reluHead
  simp_rw [relu_score_selection ℓ B hB target source score hscore]
  by_cases hq : q=target
  · subst q
    simp
  · simp [hq]

#print axioms token_angle_difference
#print axioms token_angle_range
#print axioms token_cos_nonnegative
#print axioms token_cos_gap
#print axioms positional_penalty_selected
#print axioms positional_penalty_off_target
#print axioms relu_score_selection
#print axioms positional_query_key_dot
#print axioms relu_head_selection
end GeneralizationCheck
