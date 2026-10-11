module

public import ICLGeneralization.GeneralFFNStability

@[expose] public section
open Matrix
namespace GeneralizationCheck

noncomputable def scheduleFactor (s0 : ℝ) : ℝ := 2+1/s0
noncomputable def projectionRadius (w : ℕ) (κ s0 B : ℝ) : ℝ := (w : ℝ)*(scheduleFactor s0*κ)*B
noncomputable def projectionSensitivity (w : ℕ) (κ s0 B C : ℝ) : ℝ :=
  (w : ℝ)*(scheduleFactor s0*B+scheduleFactor s0*κ*C)
noncomputable def mhaRadius (w m ℓ : ℕ) (κ s0 B : ℝ) : ℝ :=
  (m : ℝ)*(projectionRadius w κ s0 B+(ℓ : ℝ)*(w : ℝ)*(projectionRadius w κ s0 B)^3)
noncomputable def mhaSensitivity (w m ℓ : ℕ) (κ s0 B C : ℝ) : ℝ :=
  (m : ℝ)*(1+4*(w : ℝ)*(projectionRadius w κ s0 B)^2+
    3*(ℓ : ℝ)*(w : ℝ)*(projectionRadius w κ s0 B)^2)*projectionSensitivity w κ s0 B C

theorem projection_radius_nonnegative (w : ℕ) (κ s0 B : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) :
    0 ≤ projectionRadius w κ s0 B := by unfold projectionRadius scheduleFactor; positivity

theorem projection_sensitivity_nonnegative (w : ℕ) (κ s0 B C : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ projectionSensitivity w κ s0 B C := by unfold projectionSensitivity scheduleFactor; positivity

theorem mha_radius_nonnegative (w m ℓ : ℕ) (κ s0 B : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) : 0 ≤ mhaRadius w m ℓ κ s0 B := by
  have h := projection_radius_nonnegative w κ s0 B hκ hs0 hB
  unfold mhaRadius
  positivity

theorem mha_sensitivity_nonnegative (w m ℓ : ℕ) (κ s0 B C : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) (hC : 0 ≤ C) : 0 ≤ mhaSensitivity w m ℓ κ s0 B C := by
  have h := projection_sensitivity_nonnegative w κ s0 B C hκ hs0 hB hC
  unfold mhaSensitivity
  positivity

theorem general_projection_bound {D w L F m ℓ : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (i : Fin m) (h : Fin 3) (H : Fin ℓ → Fin w → ℝ)
    (κ s0 a s B : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (hθ : ∀ p, |θ p| ≤ κ) (hH : ∀ q r, |H q r| ≤ B) (q : Fin ℓ) (r : Fin w) :
    |((generalScheduledMatrix θ k i h).eval a s).mulVec (H q) r| ≤ projectionRadius w κ s0 B := by
  exact matrix_action_bound _ _ _ _ (show 0 ≤ (2+1/s0)*κ by positivity)
    (fun r c => scheduled_matrix_abs_bound _ κ a s s0 hκ hs0 ha hs
      (fun r c => ⟨hθ _,hθ _,hθ _⟩) r c) (hH q) r

theorem general_projection_perturbation {D w L F m ℓ : ℕ} (θ θ' : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (i : Fin m) (h : Fin 3) (H H' : Fin ℓ → Fin w → ℝ)
    (κ s0 a s B C ε : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (hε : 0 ≤ ε) (hθ' : ∀ p, |θ' p| ≤ κ) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (hH : ∀ q r, |H q r| ≤ B) (hd : ∀ q r, |H q r-H' q r| ≤ C*ε) (q : Fin ℓ) (r : Fin w) :
    |((generalScheduledMatrix θ k i h).eval a s).mulVec (H q) r-
      ((generalScheduledMatrix θ' k i h).eval a s).mulVec (H' q) r| ≤
      projectionSensitivity w κ s0 B C*ε := by
  have hh := matrix_action_perturbation
    ((generalScheduledMatrix θ k i h).eval a s) ((generalScheduledMatrix θ' k i h).eval a s)
    (H q) (H' q) (scheduleFactor s0*κ) B (scheduleFactor s0*ε) (C*ε)
    (show 0 ≤ (2+1/s0)*κ by positivity)
    (fun r c => scheduled_matrix_abs_bound _ κ a s s0 hκ hs0 ha hs
      (fun r c => ⟨hθ' _,hθ' _,hθ' _⟩) r c) (hH q)
    (fun r c => scheduled_matrix_perturbation _ _ ε a s s0 hε hs0 ha hs
      (fun r c => ⟨he _,he _,he _⟩) r c) (hd q) r
  exact hh.trans_eq (by unfold projectionSensitivity; ring)

theorem general_mha_bound {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 B : ℝ) (H : Fin ℓ → Fin w → ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hB : 0 ≤ B)
    (hθ : ∀ p, |θ p| ≤ κ) (hH : ∀ q r, |H q r| ≤ B) (q : Fin ℓ) (r : Fin w) :
    |generalMHA θ k softmax mask a s H q r| ≤ mhaRadius w m ℓ κ s0 B := by
  let V := projectionRadius w κ s0 B
  have hV : 0 ≤ V := projection_radius_nonnegative w κ s0 B hκ hs0 hB
  have hp (i : Fin m) (h : Fin 3) := general_projection_bound θ k i h H κ s0 a s B hκ hs0 ha hs hθ hH
  unfold generalMHA
  apply finite_sum_abs_bound
  intro i
  cases softmax
  · have hh := relu_attention_bound _ _ _ H V hV (hp i 0) (hp i 1) (hp i 2) q r
    exact hh.trans (le_add_of_nonneg_left hV)
  · have hh := softmax_attention_bound hn ((generalHead θ k i).query.eval a s)
      ((generalHead θ k i).key.eval a s) ((generalHead θ k i).value.eval a s) mask H V (hp i 2) q r
    exact hh.trans (le_add_of_nonneg_right (by positivity))

theorem general_mha_perturbation {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ θ' : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 B C ε : ℝ) (H H' : Fin ℓ → Fin w → ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hθ : ∀ p, |θ p| ≤ κ) (hθ' : ∀ p, |θ' p| ≤ κ) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (hH : ∀ q r, |H q r| ≤ B) (hH' : ∀ q r, |H' q r| ≤ B)
    (hd : ∀ q r, |H q r-H' q r| ≤ C*ε) (q : Fin ℓ) (r : Fin w) :
    |generalMHA θ k softmax mask a s H q r-generalMHA θ' k softmax mask a s H' q r| ≤
      mhaSensitivity w m ℓ κ s0 B C*ε := by
  let V := projectionRadius w κ s0 B
  let E := projectionSensitivity w κ s0 B C*ε
  have hV : 0 ≤ V := projection_radius_nonnegative w κ s0 B hκ hs0 hB
  have hE : 0 ≤ E := mul_nonneg (projection_sensitivity_nonnegative w κ s0 B C hκ hs0 hB hC) hε
  have hp (i : Fin m) (h : Fin 3) := general_projection_bound θ k i h H κ s0 a s B hκ hs0 ha hs hθ hH
  have hp' (i : Fin m) (h : Fin 3) := general_projection_bound θ' k i h H' κ s0 a s B hκ hs0 ha hs hθ' hH'
  have hdiff (i : Fin m) (h : Fin 3) := general_projection_perturbation θ θ' k i h H H'
    κ s0 a s B C ε hκ hs0 ha hs hε hθ' he hH hd
  have hh : |generalMHA θ k softmax mask a s H q r-generalMHA θ' k softmax mask a s H' q r| ≤
      (m : ℝ)*((1+4*(w : ℝ)*V^2+3*(ℓ : ℝ)*(w : ℝ)*V^2)*E) := by
    unfold generalMHA
    rw [← Finset.sum_sub_distrib]
    apply finite_sum_abs_bound
    intro i
    cases softmax
    · have h := relu_attention_perturbation _ _ _ _ _ _ H H' V E hV hE
        (hp i 0) (hp' i 0) (hp i 1) (hp' i 1) (hp i 2) (hp' i 2)
        (hdiff i 0) (hdiff i 1) (hdiff i 2) q r
      apply h.trans
      apply mul_le_mul_of_nonneg_right _ hE
      have : 0 ≤ 1+4*(w : ℝ)*V^2 := by positivity
      linarith
    · have h := softmax_attention_perturbation hn _ _ _ _ _ _ mask H H' V E hV hE
        (hp' i 0) (hp i 1) (hp i 2) (hdiff i 0) (hdiff i 1) (hdiff i 2) q r
      exact h.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity : 0 ≤ 3*(ℓ : ℝ)*(w : ℝ)*V^2)) hE)
  exact hh.trans_eq (by unfold mhaSensitivity E V; ring)

#print axioms projection_radius_nonnegative
#print axioms projection_sensitivity_nonnegative
#print axioms mha_radius_nonnegative
#print axioms mha_sensitivity_nonnegative
#print axioms general_projection_bound
#print axioms general_projection_perturbation
#print axioms general_mha_bound
#print axioms general_mha_perturbation
end GeneralizationCheck
