module

public import ICLGeneralization.PositionalSelection
public import ICLGeneralization.RealizationReadout

@[expose] public section

namespace GeneralizationCheck

/- Data rows of the embedding. The two sinusoidal rows and the constant row
   remain fixed throughout the four ReLU blocks. The unused auxiliary row is
   zero. Together the row count is D+1+D+1+1+2+1 = 2D+6. -/
structure RealizationState (n D : ℕ) where
  data : Fin (n+1) → Fin D → ℝ
  value : Fin (n+1) → ℝ
  difference : Fin (n+1) → Fin D → ℝ
  logit : Fin (n+1) → ℝ

noncomputable def initialState (n D : ℕ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    RealizationState n D where
  data q := if h : q.val < n then x ⟨q.val, h⟩ else y
  value _ := 0
  difference _ _ := 0
  logit _ := 0

theorem initial_prompt_data (n D : ℕ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) (i : Fin n) :
    (initialState n D x y).data i.castSucc = x i := by
  simp [initialState, i.isLt]

theorem initial_query_data (n D : ℕ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    (initialState n D x y).data (Fin.last n) = y := by
  simp [initialState]

noncomputable def copyHead (n : ℕ) (target source : Fin (n+1))
    (value : Fin (n+1) → ℝ) (q : Fin (n+1)) : ℝ :=
  reluHead (n+1) 1 target source (fun _ _ => 1) value q

theorem copy_head_exact (n : ℕ) (target source : Fin (n+1))
    (value : Fin (n+1) → ℝ) (q : Fin (n+1)) :
    copyHead n target source value q = if q=target then value source else 0 := by
  unfold copyHead
  rw [relu_head_selection (n+1) 1 (by norm_num) target source _ (by intros; rfl)]
  norm_num

theorem prompt_copy_sum (n : ℕ) (source : Fin n → Fin (n+1))
    (value : Fin (n+1) → ℝ) (i : Fin n) :
    (∑ k, copyHead n k.castSucc (source k) value i.castSucc) = value (source i) := by
  classical
  simp_rw [copy_head_exact]
  simp

theorem query_copy_sum (n : ℕ) (source : Fin n → Fin (n+1))
    (value : Fin (n+1) → ℝ) :
    (∑ k, copyHead n k.castSucc (source k) value (Fin.last n)) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  rw [copy_head_exact, ite_eq_right (Ne.symm (Fin.castSucc_ne_last k))]

noncomputable def blockOne (n D : ℕ) (j : Fin D) (H : RealizationState n D) :
    RealizationState n D :=
  { H with value := fun q => H.value q+
      ∑ i : Fin n, copyHead n i.castSucc i.castSucc (fun k => H.data k j) q }

noncomputable def blockTwo (n D : ℕ) (a : ℝ) (H : RealizationState n D) :
    RealizationState n D :=
  { H with difference := fun q r => H.difference q r+
      ∑ i : Fin n, copyHead n i.castSucc i.castSucc (fun k => -a*H.data k r) q }

noncomputable def blockThree (n D : ℕ) (H : RealizationState n D) :
    RealizationState n D :=
  { H with difference := fun q r => H.difference q r+
      ∑ i : Fin n, copyHead n i.castSucc (Fin.last n) (fun k => H.data k r) q }

noncomputable def preLogitState (n D : ℕ) (j : Fin D) (a : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) : RealizationState n D :=
  blockThree n D (blockTwo n D a (blockOne n D j (initialState n D x y)))

theorem three_blocks_prompt_value (n D : ℕ) (j : Fin D) (a : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) (i : Fin n) :
    (preLogitState n D j a x y).value i.castSucc = x i j := by
  simp only [preLogitState, blockThree, blockTwo, blockOne, initialState,
    zero_add, prompt_copy_sum]
  simp [i.isLt]

theorem three_blocks_query_value (n D : ℕ) (j : Fin D) (a : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    (preLogitState n D j a x y).value (Fin.last n) = 0 := by
  simp [preLogitState, blockThree, blockTwo, blockOne, initialState, query_copy_sum]

theorem three_blocks_prompt_difference (n D : ℕ) (j : Fin D) (a : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) (i : Fin n) (r : Fin D) :
    (preLogitState n D j a x y).difference i.castSucc r = y r-a*x i r := by
  simp only [preLogitState, blockThree, blockTwo, blockOne, initialState,
    zero_add, prompt_copy_sum]
  simp [i.isLt]
  ring

theorem three_blocks_query_difference (n D : ℕ) (j : Fin D) (a : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) (r : Fin D) :
    (preLogitState n D j a x y).difference (Fin.last n) r = 0 := by
  simp [preLogitState, blockThree, blockTwo, blockOne, initialState, query_copy_sum]

noncomputable def distanceScore (n D : ℕ) (M s : ℝ) (H : RealizationState n D)
    (q k : Fin (n+1)) : ℝ :=
  M-(∑ r, (H.difference q r/s)*(H.difference k r/s))/2

theorem distance_score_upper_bound (n D : ℕ) (M s : ℝ) (H : RealizationState n D)
    (henergy : ∀ q, (∑ r, (H.difference q r/s)^2) ≤ 2*M) (q k : Fin (n+1)) :
    distanceScore n D M s H q k ≤ 2*M := by
  have hcross : -(∑ r, (H.difference q r/s)*(H.difference k r/s)) ≤
      ((∑ r, (H.difference q r/s)^2)+(∑ r, (H.difference k r/s)^2))/2 := by
    have h := Finset.sum_nonneg (s := Finset.univ)
      (fun r (_ : r ∈ Finset.univ) => sq_nonneg (H.difference q r/s+H.difference k r/s))
    simp only [add_sq, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at h
    linarith
  unfold distanceScore
  linarith [henergy q, henergy k]

noncomputable def blockFour (n D : ℕ) (M s : ℝ) (H : RealizationState n D) :
    RealizationState n D :=
  { H with logit := fun q => H.logit q+
      ∑ i : Fin n, (reluHead (n+1) (2*M) i.castSucc i.castSucc
        (distanceScore n D M s H) (fun _ => 1) q) }

theorem block_four_prompt_logit (n D : ℕ) (M s : ℝ) (hM : 0 ≤ M)
    (H : RealizationState n D) (hlogit : ∀ q, H.logit q=0)
    (henergy : ∀ q, (∑ r, (H.difference q r/s)^2) ≤ 2*M) (i : Fin n) :
    (blockFour n D M s H).logit i.castSucc =
      M-(∑ r, (H.difference i.castSucc r/s)^2)/2 := by
  classical
  unfold blockFour
  simp only [hlogit, zero_add]
  simp_rw [relu_head_selection (n+1) (2*M) (by positivity) _ _ _
    (distance_score_upper_bound n D M s H henergy)]
  simp only [mul_one, Fin.castSucc_inj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  unfold distanceScore
  simp only [← sq]
  exact max_eq_right (by linarith [henergy i.castSucc])

noncomputable def blockFiveOutput (n D : ℕ) (b : ℝ) (H : RealizationState n D) : ℝ :=
  let z := H.value (Fin.last n)+
    softmaxReadout n (fun i => H.logit i.castSucc) (fun i => H.value i.castSucc)
  z+clippingCorrection b z

noncomputable def constructedOutput (n D : ℕ) (j : Fin D) (a s M b : ℝ)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) : ℝ :=
  blockFiveOutput n D b (blockFour n D M s (preLogitState n D j a x y))

theorem pre_logit_energy (n D : ℕ) (j : Fin D) (a s M : ℝ) (hM : 0 ≤ M)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ)
    (hy : ∀ i, (∑ r, ((y r-a*x i r)/s)^2) ≤ 2*M) :
    ∀ q, (∑ r, ((preLogitState n D j a x y).difference q r/s)^2) ≤ 2*M := by
  intro q
  refine Fin.lastCases ?_ (fun i => ?_) q
  · simp_rw [three_blocks_query_difference]
    simp only [zero_div, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero]
    linarith
  · simp_rw [three_blocks_prompt_difference]
    exact hy i

theorem five_block_kernel_exact (n D : ℕ) (hn : 0 < n) (j : Fin D)
    (a s M b : ℝ) (hM : 0 ≤ M) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ)
    (hx : ∀ i r, -b ≤ x i r ∧ x i r ≤ b)
    (hy : ∀ i, (∑ r, ((y r-a*x i r)/s)^2) ≤ 2*M) :
    constructedOutput n D j a s M b x y =
      softmaxReadout n (fun i => -(∑ r, (y r-a*x i r)^2)/(2*s^2)) (fun i => x i j) := by
  let H := preLogitState n D j a x y
  have hE := pre_logit_energy n D j a s M hM x y hy
  have hzero : ∀ q, H.logit q=0 := by
    intro q
    rfl
  have hlog (i : Fin n) : (blockFour n D M s H).logit i.castSucc =
      M+(-(∑ r, (y r-a*x i r)^2)/(2*s^2)) := by
    rw [block_four_prompt_logit n D M s hM H hzero hE i]
    dsimp [H]
    simp_rw [three_blocks_prompt_difference, div_pow]
    rw [← Finset.sum_div]
    ring
  have hval (i : Fin n) : (blockFour n D M s H).value i.castSucc = x i j :=
    three_blocks_prompt_value n D j a x y i
  have hquery : (blockFour n D M s H).value (Fin.last n)=0 :=
    three_blocks_query_value n D j a x y
  unfold constructedOutput blockFiveOutput
  change (blockFour n D M s H).value (Fin.last n)+
      softmaxReadout n (fun i => (blockFour n D M s H).logit i.castSucc)
        (fun i => (blockFour n D M s H).value i.castSucc)+
      clippingCorrection b ((blockFour n D M s H).value (Fin.last n)+
        softmaxReadout n (fun i => (blockFour n D M s H).logit i.castSucc)
          (fun i => (blockFour n D M s H).value i.castSucc)) = _
  simp_rw [hquery, zero_add, hlog, hval]
  exact clipped_softmax_exact n hn _ _ M b (fun i => hx i j)

theorem five_block_output_global_bound (n D : ℕ) (j : Fin D) (a s M b : ℝ)
    (hb : 0 ≤ b) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    -b ≤ constructedOutput n D j a s M b x y ∧ constructedOutput n D j a s M b x y ≤ b := by
  exact clipping_global_bounds b _ hb

#print axioms initial_prompt_data
#print axioms initial_query_data
#print axioms copy_head_exact
#print axioms prompt_copy_sum
#print axioms query_copy_sum
#print axioms three_blocks_prompt_value
#print axioms three_blocks_query_value
#print axioms three_blocks_prompt_difference
#print axioms three_blocks_query_difference
#print axioms distance_score_upper_bound
#print axioms block_four_prompt_logit
#print axioms pre_logit_energy
#print axioms five_block_kernel_exact
#print axioms five_block_output_global_bound
end GeneralizationCheck
