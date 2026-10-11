module

public import ICLGeneralization.FiveBlockRealization
public import ICLGeneralization.Core
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace GeneralizationCheck

theorem clean_difference_norm_bound (D : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (u v : EuclideanSpace ℝ (Fin D))
    (hu : ∀ r, -b ≤ u r ∧ u r ≤ b) (hv : ∀ r, -b ≤ v r ∧ v r ≤ b) :
    ‖u-v‖ ≤ 2*b*Real.sqrt (D : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply]
  have h := vector_error_bound D (fun r => u r) (fun r => v r) b b hu hv
  have he : (D : ℝ)*(b+b)^2 = (2*b*Real.sqrt (D : ℝ))^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  exact h.trans_eq he

theorem normalized_query_distance_bound (D : ℕ) (b C a s s0 : ℝ)
    (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (z x eps : EuclideanSpace ℝ (Fin D))
    (hz : ∀ r, -b ≤ z r ∧ z r ≤ b) (hx : ∀ r, -b ≤ x r ∧ x r ≤ b)
    (heps : ‖eps‖ ≤ C) :
    ‖a • z+s • eps-a • x‖/s ≤ 2*b*Real.sqrt (D : ℝ)/s0+C := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  have hvec : a • z+s • eps-a • x = a • (z-x)+s • eps := by
    ext r
    simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [hvec]
  have hnorm : ‖a • (z-x)+s • eps‖ ≤ a*(2*b*Real.sqrt (D : ℝ))+s*C := by
    calc
      _ ≤ ‖a • (z-x)‖+‖s • eps‖ := norm_add_le _ _
      _ = a*‖z-x‖+s*‖eps‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha.1, abs_of_pos hsp]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (clean_difference_norm_bound D b hb z x hz hx) ha.1)
        (mul_le_mul_of_nonneg_left heps hsp.le)
  have hratio : a*(2*b*Real.sqrt (D : ℝ))/s ≤ 2*b*Real.sqrt (D : ℝ)/s0 := by
    calc
      _ ≤ (2*b*Real.sqrt (D : ℝ))/s :=
        div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) ha.2) hsp.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hs0 hs
  have hdiv := div_le_div_of_nonneg_right hnorm hsp.le
  have hid : (a*(2*b*Real.sqrt (D : ℝ))+s*C)/s = a*(2*b*Real.sqrt (D : ℝ))/s+C := by
    field_simp
  rw [hid] at hdiv
  linarith

noncomputable def realizationM (D : ℕ) (b R s0 C : ℝ) : ℝ :=
  max (max 1 R) ((2*b*Real.sqrt (D : ℝ)/s0+C)^2/2)

theorem realization_M_nonnegative (D : ℕ) (b R s0 C : ℝ) :
    0 ≤ realizationM D b R s0 C := by
  unfold realizationM
  exact le_trans (by positivity : 0 ≤ (2*b*Real.sqrt (D : ℝ)/s0+C)^2/2)
    (le_max_right _ _)

theorem query_region_energy (D : ℕ) (b R C a s s0 : ℝ)
    (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (z x eps : EuclideanSpace ℝ (Fin D))
    (hz : ∀ r, -b ≤ z r ∧ z r ≤ b) (hx : ∀ r, -b ≤ x r ∧ x r ≤ b)
    (heps : ‖eps‖ ≤ C) :
    (∑ r, (((a • z+s • eps) r-a*x r)/s)^2) ≤ 2*realizationM D b R s0 C := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  have hnorm := normalized_query_distance_bound D b C a s s0 hb ha hs0 hs z x eps hz hx heps
  have hsq := pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hsp.le) hnorm 2
  have he : (∑ r, (((a • z+s • eps) r-a*x r)/s)^2) = (‖a • z+s • eps-a • x‖/s)^2 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [he]
  have hM : (2*b*Real.sqrt (D : ℝ)/s0+C)^2/2 ≤ realizationM D b R s0 C :=
    le_max_right _ _
  linarith

theorem five_blocks_exact_on_query_region (n D : ℕ) (hn : 0 < n) (j : Fin D)
    (b R C a s s0 : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1)
    (hs0 : 0 < s0) (hs : s0 ≤ s)
    (x : Fin n → EuclideanSpace ℝ (Fin D)) (z eps : EuclideanSpace ℝ (Fin D))
    (hx : ∀ i r, -b ≤ x i r ∧ x i r ≤ b)
    (hz : ∀ r, -b ≤ z r ∧ z r ≤ b) (heps : ‖eps‖ ≤ C) :
    constructedOutput n D j a s (realizationM D b R s0 C) b
      (fun i r => x i r) (fun r => (a • z+s • eps) r) =
    softmaxReadout n
      (fun i => -(∑ r, ((a • z+s • eps) r-a*x i r)^2)/(2*s^2)) (fun i => x i j) := by
  apply five_block_kernel_exact n D hn j a s _ b (realization_M_nonnegative D b R s0 C)
    _ _ hx
  intro i
  exact query_region_energy D b R C a s s0 hb ha hs0 hs z (x i) eps hz (hx i) heps

theorem vector_five_blocks_exact_on_query_region (n D : ℕ) (hn : 0 < n)
    (b R C a s s0 : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1)
    (hs0 : 0 < s0) (hs : s0 ≤ s)
    (x : Fin n → EuclideanSpace ℝ (Fin D)) (z eps : EuclideanSpace ℝ (Fin D))
    (hx : ∀ i r, -b ≤ x i r ∧ x i r ≤ b)
    (hz : ∀ r, -b ≤ z r ∧ z r ≤ b) (heps : ‖eps‖ ≤ C) :
    (fun j => constructedOutput n D j a s (realizationM D b R s0 C) b
      (fun i r => x i r) (fun r => (a • z+s • eps) r)) =
    (fun j => softmaxReadout n
      (fun i => -(∑ r, ((a • z+s • eps) r-a*x i r)^2)/(2*s^2)) (fun i => x i j)) := by
  funext j
  exact five_blocks_exact_on_query_region n D hn j b R C a s s0 hb ha hs0 hs x z eps hx hz heps

#print axioms clean_difference_norm_bound
#print axioms normalized_query_distance_bound
#print axioms realization_M_nonnegative
#print axioms query_region_energy
#print axioms five_blocks_exact_on_query_region
#print axioms vector_five_blocks_exact_on_query_region
end GeneralizationCheck
