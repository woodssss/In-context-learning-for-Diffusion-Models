module

public import ICLGeneralization.GeneralTransformer

@[expose] public section
open Matrix
namespace GeneralizationCheck

noncomputable def ffnRadius (w : ℕ) (κ B : ℝ) : ℕ → ℝ
  | 0 => B
  | j+1 => κ+(w : ℝ)*κ*ffnRadius w κ B j

noncomputable def ffnSensitivity (w : ℕ) (κ B C : ℝ) : ℕ → ℝ
  | 0 => C
  | j+1 => (w : ℝ)*ffnRadius w κ B j+1+(w : ℝ)*κ*ffnSensitivity w κ B C j

theorem ffn_radius_nonnegative (w : ℕ) (κ B : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B) (j : ℕ) :
    0 ≤ ffnRadius w κ B j := by induction j with | zero => exact hB | succ j ih => dsimp [ffnRadius]; positivity

theorem ffn_sensitivity_nonnegative (w : ℕ) (κ B C : ℝ) (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hC : 0 ≤ C) (j : ℕ) :
    0 ≤ ffnSensitivity w κ B C j := by
  induction j with
  | zero => exact hC
  | succ j ih =>
    have h := ffn_radius_nonnegative w κ B hκ hB j
    dsimp [ffnSensitivity]
    positivity

theorem general_affine_bound {D w L F m : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (j : Fin F) (relu : Bool) (x : Fin w → ℝ) (κ B : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hθ : ∀ p, |θ p| ≤ κ) (hx : ∀ r, |x r| ≤ B) (r : Fin w) :
    |generalAffine θ k j relu x r| ≤ κ+(w : ℝ)*κ*B := by
  have hm := matrix_action_bound (generalAffineMatrix θ k j) x κ B hκ (fun r c => hθ _) hx r
  have hb : |generalAffineBias θ k j r| ≤ κ := hθ _
  have ha : |(generalAffineMatrix θ k j).mulVec x r+generalAffineBias θ k j r| ≤ κ+(w : ℝ)*κ*B :=
    (abs_add_le _ _).trans ((add_le_add hm hb).trans_eq (by ring))
  cases relu
  · exact ha
  · exact relu_abs_bound _ _ (by positivity) ha

theorem general_affine_perturbation {D w L F m : ℕ} (θ θ' : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (j : Fin F) (relu : Bool) (x x' : Fin w → ℝ) (κ B C ε : ℝ)
    (hκ : 0 ≤ κ) (_hB : 0 ≤ B) (_hC : 0 ≤ C) (_hε : 0 ≤ ε)
    (hθ' : ∀ p, |θ' p| ≤ κ) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (hx : ∀ r, |x r| ≤ B) (hd : ∀ r, |x r-x' r| ≤ C*ε) (r : Fin w) :
    |generalAffine θ k j relu x r-generalAffine θ' k j relu x' r| ≤
      ((w : ℝ)*B+1+(w : ℝ)*κ*C)*ε := by
  have hm := matrix_action_perturbation (generalAffineMatrix θ k j) (generalAffineMatrix θ' k j)
    x x' κ B ε (C*ε) hκ (fun r c => hθ' _) hx (fun r c => he _) hd r
  have hb : |generalAffineBias θ k j r-generalAffineBias θ' k j r| ≤ ε := he _
  have ha : |((generalAffineMatrix θ k j).mulVec x r+generalAffineBias θ k j r)-
      ((generalAffineMatrix θ' k j).mulVec x' r+generalAffineBias θ' k j r)| ≤
        ((w : ℝ)*B+1+(w : ℝ)*κ*C)*ε := by
    calc
      _ = |((generalAffineMatrix θ k j).mulVec x r-(generalAffineMatrix θ' k j).mulVec x' r)+
        (generalAffineBias θ k j r-generalAffineBias θ' k j r)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ (w : ℝ)*(ε*B+κ*(C*ε))+ε := add_le_add hm hb
      _ = _ := by ring
  cases relu
  · exact ha
  · exact relu_perturbation _ _ _ ha

theorem general_ffn_bound {D w L F m : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (activation : Fin F → Bool) (x : Fin w → ℝ) (κ B : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hθ : ∀ p, |θ p| ≤ κ) (hx : ∀ r, |x r| ≤ B)
    (j : ℕ) (hj : j ≤ F) : ∀ r, |generalFFNState θ k activation x j r| ≤ ffnRadius w κ B j := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    have hj' : j < F := by omega
    have hi := ih (by omega)
    intro r
    simp only [generalFFNState,dite_eq_left hj']
    exact general_affine_bound θ k ⟨j,hj'⟩ _ _ κ _ hκ
      (ffn_radius_nonnegative w κ B hκ hB j) hθ hi r

theorem general_ffn_perturbation {D w L F m : ℕ} (θ θ' : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (activation : Fin F → Bool) (x x' : Fin w → ℝ) (κ B C ε : ℝ)
    (hκ : 0 ≤ κ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hθ : ∀ p, |θ p| ≤ κ) (hθ' : ∀ p, |θ' p| ≤ κ) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (hx : ∀ r, |x r| ≤ B) (hd : ∀ r, |x r-x' r| ≤ C*ε)
    (j : ℕ) (hj : j ≤ F) : ∀ r,
    |generalFFNState θ k activation x j r-generalFFNState θ' k activation x' j r| ≤
      ffnSensitivity w κ B C j*ε := by
  induction j with
  | zero => exact hd
  | succ j ih =>
    have hj' : j < F := by omega
    intro r
    simp only [generalFFNState,dite_eq_left hj']
    exact general_affine_perturbation θ θ' k ⟨j,hj'⟩ _ _ _ κ _ _ ε hκ
      (ffn_radius_nonnegative w κ B hκ hB j) (ffn_sensitivity_nonnegative w κ B C hκ hB hC j)
      hε hθ' he (general_ffn_bound θ k activation x κ B hκ hB hθ hx j (by omega))
      (ih (by omega)) r

#print axioms ffn_radius_nonnegative
#print axioms ffn_sensitivity_nonnegative
#print axioms general_affine_bound
#print axioms general_affine_perturbation
#print axioms general_ffn_bound
#print axioms general_ffn_perturbation
end GeneralizationCheck
