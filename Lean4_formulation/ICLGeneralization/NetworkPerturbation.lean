module

public import ICLGeneralization.SoftmaxStability
public import ICLGeneralization.ScheduledMatrices

@[expose] public section
open Matrix
namespace GeneralizationCheck

theorem finite_sum_abs_bound (n : ℕ) (f : Fin n → ℝ) (B : ℝ) (h : ∀ i, |f i| ≤ B) :
    |∑ i, f i| ≤ (n : ℝ)*B := by
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp))

theorem product_perturbation (u u' v v' K B E F : ℝ) (hK : 0 ≤ K)
    (hu : |u'| ≤ K) (hv : |v| ≤ B) (he : |u-u'| ≤ E) (hf : |v-v'| ≤ F) :
    |u*v-u'*v'| ≤ E*B+K*F := by
  have h1 : |(u-u')*v| ≤ E*B := by
    rw [abs_mul]
    exact mul_le_mul he hv (abs_nonneg _) (le_trans (abs_nonneg _) he)
  have h2 : |u'*(v-v')| ≤ K*F := by
    rw [abs_mul]
    exact mul_le_mul hu hf (abs_nonneg _) hK
  calc
    _ = |(u-u')*v+u'*(v-v')| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

theorem matrix_action_bound {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ)
    (x : Fin e → ℝ) (K B : ℝ) (hK : 0 ≤ K)
    (hA : ∀ i j, |A i j| ≤ K) (hx : ∀ j, |x j| ≤ B) (i : Fin d) :
    |A.mulVec x i| ≤ (e : ℝ)*K*B := by
  unfold Matrix.mulVec dotProduct
  have h := finite_sum_abs_bound e (fun j => A i j*x j) (K*B)
    (fun j => by rw [abs_mul]; exact mul_le_mul (hA i j) (hx j) (abs_nonneg _) hK)
  exact h.trans_eq (by ring)

theorem matrix_action_perturbation {d e : ℕ} (A A' : Matrix (Fin d) (Fin e) ℝ)
    (x x' : Fin e → ℝ) (K B E F : ℝ) (hK : 0 ≤ K)
    (hA : ∀ i j, |A' i j| ≤ K) (hx : ∀ j, |x j| ≤ B)
    (he : ∀ i j, |A i j-A' i j| ≤ E) (hf : ∀ j, |x j-x' j| ≤ F) (i : Fin d) :
    |A.mulVec x i-A'.mulVec x' i| ≤ (e : ℝ)*(E*B+K*F) := by
  unfold Matrix.mulVec dotProduct
  rw [← Finset.sum_sub_distrib]
  exact finite_sum_abs_bound e _ _
    (fun j => product_perturbation _ _ _ _ K B E F hK (hA i j) (hx j) (he i j) (hf j))

theorem relu_abs_bound (x B : ℝ) (hB : 0 ≤ B) (hx : |x| ≤ B) : |max 0 x| ≤ B := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le hB (le_trans (le_abs_self _) hx)

theorem relu_perturbation (x y E : ℝ) (h : |x-y| ≤ E) : |max 0 x-max 0 y| ≤ E := by
  simpa only [max_comm] using (abs_max_sub_max_le_abs x y 0).trans h

theorem scheduled_matrix_abs_bound {d : ℕ} (A : ScheduledMatrix d) (κ a s s0 : ℝ)
    (_hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (hA : ∀ i j, |A.base i j| ≤ κ ∧ |A.alpha i j| ≤ κ ∧ |A.reciprocal i j| ≤ κ)
    (i j : Fin d) : |A.eval a s i j| ≤ (2+1/s0)*κ := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  have hb := hA i j
  have hα : |a*A.alpha i j| ≤ κ := by
    rw [abs_mul,abs_of_nonneg ha.1]
    exact (mul_le_mul ha.2 hb.2.1 (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hσ : |(1/s)*A.reciprocal i j| ≤ (1/s0)*κ := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/s)]
    exact mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hs0 hs) hb.2.2 (abs_nonneg _) (by positivity)
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hb.1 hα)) hσ).trans_eq (by ring))

theorem scheduled_matrix_perturbation {d : ℕ} (A A' : ScheduledMatrix d) (E a s s0 : ℝ)
    (hE : 0 ≤ E) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (he : ∀ i j, |A.base i j-A'.base i j| ≤ E ∧ |A.alpha i j-A'.alpha i j| ≤ E ∧
      |A.reciprocal i j-A'.reciprocal i j| ≤ E) (i j : Fin d) :
    |A.eval a s i j-A'.eval a s i j| ≤ (2+1/s0)*E := by
  let B : ScheduledMatrix d := ⟨A.base-A'.base,A.alpha-A'.alpha,A.reciprocal-A'.reciprocal⟩
  have h := scheduled_matrix_abs_bound B E a s s0 hE hs0 ha hs
    (fun i j => he i j) i j
  convert h using 1
  unfold ScheduledMatrix.eval B
  simp only [Matrix.sub_apply]
  congr 1
  ring

#print axioms finite_sum_abs_bound
#print axioms product_perturbation
#print axioms matrix_action_bound
#print axioms matrix_action_perturbation
#print axioms relu_abs_bound
#print axioms relu_perturbation
#print axioms scheduled_matrix_abs_bound
#print axioms scheduled_matrix_perturbation
end GeneralizationCheck
