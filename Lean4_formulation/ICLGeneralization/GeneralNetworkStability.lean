module

public import ICLGeneralization.GeneralAttentionStability

@[expose] public section
namespace GeneralizationCheck

noncomputable def blockRadius (w m ℓ F : ℕ) (κ s0 B : ℝ) : ℝ :=
  let Z := B+mhaRadius w m ℓ κ s0 B
  Z+ffnRadius w κ Z F
noncomputable def blockSensitivity (w m ℓ F : ℕ) (κ s0 B C : ℝ) : ℝ :=
  let Z := B+mhaRadius w m ℓ κ s0 B
  let E := C+mhaSensitivity w m ℓ κ s0 B C
  E+ffnSensitivity w κ Z E F

noncomputable def networkRadius (D w m ℓ F : ℕ) (κ s0 U : ℝ) : ℕ → ℝ
  | 0 => 1+(D : ℝ)*κ*U
  | j+1 => blockRadius w m ℓ F κ s0 (networkRadius D w m ℓ F κ s0 U j)
noncomputable def networkSensitivity (D w m ℓ F : ℕ) (κ s0 U : ℝ) : ℕ → ℝ
  | 0 => (D : ℝ)*U
  | j+1 => blockSensitivity w m ℓ F κ s0 (networkRadius D w m ℓ F κ s0 U j)
      (networkSensitivity D w m ℓ F κ s0 U j)
noncomputable def transformerSensitivity (D w m ℓ F L : ℕ) (κ s0 U : ℝ) : ℝ :=
  (w : ℝ)*(networkRadius D w m ℓ F κ s0 U L+κ*networkSensitivity D w m ℓ F κ s0 U L)

theorem block_radius_nonnegative (w m ℓ F : ℕ) (κ s0 B : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) : 0 ≤ blockRadius w m ℓ F κ s0 B := by
  have h := mha_radius_nonnegative w m ℓ κ s0 B hκ hs0 hB
  exact add_nonneg (add_nonneg hB h) (ffn_radius_nonnegative _ _ _ hκ (add_nonneg hB h) _)

theorem block_sensitivity_nonnegative (w m ℓ F : ℕ) (κ s0 B C : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 ≤ blockSensitivity w m ℓ F κ s0 B C := by
  have h := mha_radius_nonnegative w m ℓ κ s0 B hκ hs0 hB
  have he := mha_sensitivity_nonnegative w m ℓ κ s0 B C hκ hs0 hB hC
  exact add_nonneg (add_nonneg hC he)
    (ffn_sensitivity_nonnegative _ _ _ _ hκ (add_nonneg hB h) (add_nonneg hC he) _)

theorem network_bounds_nonnegative (D w m ℓ F : ℕ) (κ s0 U : ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hU : 0 ≤ U) (j : ℕ) :
    0 ≤ networkRadius D w m ℓ F κ s0 U j ∧ 0 ≤ networkSensitivity D w m ℓ F κ s0 U j := by
  induction j with
  | zero => dsimp [networkRadius,networkSensitivity]; constructor <;> positivity
  | succ j ih => exact ⟨block_radius_nonnegative _ _ _ _ _ _ _ hκ hs0 ih.1,
      block_sensitivity_nonnegative _ _ _ _ _ _ _ _ hκ hs0 ih.1 ih.2⟩

theorem general_block_bound {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool) (activation : Fin F → Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 B : ℝ) (H : Fin ℓ → Fin w → ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hB : 0 ≤ B)
    (hθ : ∀ p, |θ p| ≤ κ) (hH : ∀ q r, |H q r| ≤ B) (q : Fin ℓ) (r : Fin w) :
    |generalBlock θ k softmax activation mask a s H q r| ≤ blockRadius w m ℓ F κ s0 B := by
  let Z := fun q r => H q r+generalMHA θ k softmax mask a s H q r
  have hM := general_mha_bound hn θ k softmax mask a s κ s0 B H hκ hs0 ha hs hB hθ hH
  have hZ (q : Fin ℓ) (r : Fin w) : |Z q r| ≤ B+mhaRadius w m ℓ κ s0 B :=
    (abs_add_le _ _).trans (add_le_add (hH q r) (hM q r))
  have hZ0 := add_nonneg hB (mha_radius_nonnegative w m ℓ κ s0 B hκ hs0 hB)
  exact (abs_add_le _ _).trans (add_le_add (hZ q r)
    (general_ffn_bound θ k activation (Z q) κ _ hκ hZ0 hθ (hZ q) F (le_refl _) r))

theorem general_block_perturbation {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ θ' : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool) (activation : Fin F → Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 B C ε : ℝ) (H H' : Fin ℓ → Fin w → ℝ)
    (hκ : 0 ≤ κ) (hs0 : 0 < s0) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hθ : ∀ p, |θ p| ≤ κ) (hθ' : ∀ p, |θ' p| ≤ κ) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (hH : ∀ q r, |H q r| ≤ B) (hH' : ∀ q r, |H' q r| ≤ B)
    (hd : ∀ q r, |H q r-H' q r| ≤ C*ε) (q : Fin ℓ) (r : Fin w) :
    |generalBlock θ k softmax activation mask a s H q r-generalBlock θ' k softmax activation mask a s H' q r| ≤
      blockSensitivity w m ℓ F κ s0 B C*ε := by
  let Z := fun q r => H q r+generalMHA θ k softmax mask a s H q r
  let Z' := fun q r => H' q r+generalMHA θ' k softmax mask a s H' q r
  let R := B+mhaRadius w m ℓ κ s0 B
  let E := C+mhaSensitivity w m ℓ κ s0 B C
  have hR : 0 ≤ R := add_nonneg hB (mha_radius_nonnegative w m ℓ κ s0 B hκ hs0 hB)
  have hE : 0 ≤ E := add_nonneg hC (mha_sensitivity_nonnegative w m ℓ κ s0 B C hκ hs0 hB hC)
  have hZ (q : Fin ℓ) (r : Fin w) : |Z q r| ≤ R :=
    (abs_add_le _ _).trans (add_le_add (hH q r)
      (general_mha_bound hn θ k softmax mask a s κ s0 B H hκ hs0 ha hs hB hθ hH q r))
  have hdiff (q : Fin ℓ) (r : Fin w) : |Z q r-Z' q r| ≤ E*ε := by
    calc
      _ = |(H q r-H' q r)+(generalMHA θ k softmax mask a s H q r-generalMHA θ' k softmax mask a s H' q r)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ C*ε+mhaSensitivity w m ℓ κ s0 B C*ε := add_le_add (hd q r)
        (general_mha_perturbation hn θ θ' k softmax mask a s κ s0 B C ε H H'
          hκ hs0 ha hs hB hC hε hθ hθ' he hH hH' hd q r)
      _ = _ := by dsimp [E]; ring
  have hf := general_ffn_perturbation θ θ' k activation (Z q) (Z' q) κ R E ε
    hκ hR hE hε hθ hθ' he (hZ q) (hdiff q) F (le_refl _) r
  change |(Z q r+generalFFNState θ k activation (Z q) F r)-
    (Z' q r+generalFFNState θ' k activation (Z' q) F r)| ≤ _
  calc
    _ = |(Z q r-Z' q r)+(generalFFNState θ k activation (Z q) F r-generalFFNState θ' k activation (Z' q) F r)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ E*ε+ffnSensitivity w κ R E F*ε := add_le_add (hdiff q r) hf
    _ = _ := by unfold blockSensitivity; dsimp [E,R]; ring

theorem general_embedding_bound {D w L F m ℓ : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (PE tokenMask : Fin ℓ → Fin w → ℝ) (x : Fin ℓ → Fin D → ℝ) (κ U : ℝ)
    (hκ : 0 ≤ κ) (_hU : 0 ≤ U) (hθ : ∀ p, |θ p| ≤ κ)
    (hp : ∀ q r, |PE q r| ≤ 1) (ht : ∀ q r, |tokenMask q r| ≤ 1)
    (hx : ∀ q r, |x q r| ≤ U) (q : Fin ℓ) (r : Fin w) :
    |generalEmbedding θ PE tokenMask x q r| ≤ 1+(D : ℝ)*κ*U := by
  have h := finite_sum_abs_bound D (fun c => θ (.inl (r,c))*x q c) (κ*U)
    (fun c => by rw [abs_mul]; exact mul_le_mul (hθ _) (hx q c) (abs_nonneg _) hκ)
  unfold generalEmbedding
  apply (abs_add_le _ _).trans
  apply add_le_add (hp q r)
  rw [abs_mul]
  exact (mul_le_mul (ht q r) h (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem general_embedding_perturbation {D w L F m ℓ : ℕ} (θ θ' : GeneralParameter D w L F m → ℝ)
    (PE tokenMask : Fin ℓ → Fin w → ℝ) (x : Fin ℓ → Fin D → ℝ) (U ε : ℝ)
    (_hU : 0 ≤ U) (hε : 0 ≤ ε) (he : ∀ p, |θ p-θ' p| ≤ ε)
    (ht : ∀ q r, |tokenMask q r| ≤ 1) (hx : ∀ q r, |x q r| ≤ U) (q : Fin ℓ) (r : Fin w) :
    |generalEmbedding θ PE tokenMask x q r-generalEmbedding θ' PE tokenMask x q r| ≤ (D : ℝ)*U*ε := by
  have h := finite_sum_abs_bound D (fun c => (θ (.inl (r,c))-θ' (.inl (r,c)))*x q c) (ε*U)
    (fun c => by rw [abs_mul]; exact mul_le_mul (he _) (hx q c) (abs_nonneg _) hε)
  have hdiff : generalEmbedding θ PE tokenMask x q r-generalEmbedding θ' PE tokenMask x q r =
      tokenMask q r*∑ c, (θ (.inl (r,c))-θ' (.inl (r,c)))*x q c := by
    unfold generalEmbedding
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    ring
  rw [hdiff,abs_mul]
  exact (mul_le_mul (ht q r) h (abs_nonneg _) (by norm_num)).trans_eq (by ring)

theorem general_state_bound {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 U : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hU : 0 ≤ U)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hθ : ∀ p, |θ p| ≤ κ)
    (hp : ∀ q r, |PE q r| ≤ 1) (ht : ∀ q r, |tokenMask q r| ≤ 1) (hx : ∀ q r, |x q r| ≤ U)
    (j : ℕ) (hj : j ≤ L) : ∀ q r,
    |generalState θ PE tokenMask x softmax activation mask a s j q r| ≤ networkRadius D w m ℓ F κ s0 U j := by
  induction j with
  | zero => exact general_embedding_bound θ PE tokenMask x κ U hκ hU hθ hp ht hx
  | succ j ih =>
    have hj' : j < L := by omega
    intro q r
    simp only [generalState,dite_eq_left hj']
    exact general_block_bound hn θ ⟨j,hj'⟩ _ _ mask a s κ s0 _ _ hκ hs0 ha hs
      (network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU j).1 hθ (ih (by omega)) q r

theorem general_state_perturbation {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ θ' : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 U ε : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hθ : ∀ p, |θ p| ≤ κ) (hθ' : ∀ p, |θ' p| ≤ κ)
    (he : ∀ p, |θ p-θ' p| ≤ ε) (hp : ∀ q r, |PE q r| ≤ 1)
    (ht : ∀ q r, |tokenMask q r| ≤ 1) (hx : ∀ q r, |x q r| ≤ U)
    (j : ℕ) (hj : j ≤ L) : ∀ q r,
    |generalState θ PE tokenMask x softmax activation mask a s j q r-
      generalState θ' PE tokenMask x softmax activation mask a s j q r| ≤ networkSensitivity D w m ℓ F κ s0 U j*ε := by
  induction j with
  | zero => exact general_embedding_perturbation θ θ' PE tokenMask x U ε hU hε he ht hx
  | succ j ih =>
    have hj' : j < L := by omega
    intro q r
    simp only [generalState,dite_eq_left hj']
    have hb := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU j
    exact general_block_perturbation hn θ θ' ⟨j,hj'⟩ _ _ mask a s κ s0 _ _ ε _ _ hκ hs0 ha hs hb.1 hb.2 hε
      hθ hθ' he (general_state_bound hn θ PE tokenMask x softmax activation mask a s κ s0 U hκ hs0 hU ha hs hθ hp ht hx j (by omega))
      (general_state_bound hn θ' PE tokenMask x softmax activation mask a s κ s0 U hκ hs0 hU ha hs hθ' hp ht hx j (by omega))
      (ih (by omega)) q r

theorem general_transformer_perturbation {D w L F m ℓ n : ℕ} (hn : 0 < n)
    (θ θ' : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (mask : Fin n → Fin ℓ) (a s κ s0 U ε : ℝ) (hκ : 0 ≤ κ) (hs0 : 0 < s0) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hθ : ∀ p, |θ p| ≤ κ) (hθ' : ∀ p, |θ' p| ≤ κ)
    (he : ∀ p, |θ p-θ' p| ≤ ε) (hp : ∀ q r, |PE q r| ≤ 1)
    (ht : ∀ q r, |tokenMask q r| ≤ 1) (hx : ∀ q r, |x q r| ≤ U) (q : Fin ℓ) :
    |generalTransformer θ PE tokenMask x softmax activation mask a s q-
      generalTransformer θ' PE tokenMask x softmax activation mask a s q| ≤ transformerSensitivity D w m ℓ F L κ s0 U*ε := by
  have hb := general_state_bound hn θ PE tokenMask x softmax activation mask a s κ s0 U hκ hs0 hU ha hs hθ hp ht hx L (le_refl _)
  have hd := general_state_perturbation hn θ θ' PE tokenMask x softmax activation mask a s κ s0 U ε hκ hs0 hU hε ha hs hθ hθ' he hp ht hx L (le_refl _)
  unfold generalTransformer
  rw [← Finset.sum_sub_distrib]
  have h := finite_sum_abs_bound w (fun r =>
      θ (.inr (.inr (.inr r)))*generalState θ PE tokenMask x softmax activation mask a s L q r-
      θ' (.inr (.inr (.inr r)))*generalState θ' PE tokenMask x softmax activation mask a s L q r)
    (ε*networkRadius D w m ℓ F κ s0 U L+
      κ*(networkSensitivity D w m ℓ F κ s0 U L*ε))
    (fun r => product_perturbation _ _ _ _ κ _ ε _ hκ (hθ' (.inr (.inr (.inr r)))) (hb q r) (he (.inr (.inr (.inr r)))) (hd q r))
  exact h.trans_eq (by unfold transformerSensitivity; ring)

#print axioms block_radius_nonnegative
#print axioms block_sensitivity_nonnegative
#print axioms network_bounds_nonnegative
#print axioms general_block_bound
#print axioms general_block_perturbation
#print axioms general_embedding_bound
#print axioms general_embedding_perturbation
#print axioms general_state_bound
#print axioms general_state_perturbation
#print axioms general_transformer_perturbation
end GeneralizationCheck
