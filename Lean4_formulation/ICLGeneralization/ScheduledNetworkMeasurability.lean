module

public import ICLGeneralization.MeasurableNetwork

@[expose] public section
open MeasureTheory Matrix
namespace GeneralizationCheck
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_scheduled_matrix_action {d : ℕ} (A : ScheduledMatrix d)
    (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (h : Ω → Fin d → ℝ) (hh : ∀ r, Measurable (fun ω => h ω r)) (r : Fin d) :
    Measurable (fun ω => (A.eval (a ω) (s ω)).mulVec (h ω) r) := by
  unfold Matrix.mulVec dotProduct ScheduledMatrix.eval
  apply Finset.measurable_sum
  intro c _
  have hc : Measurable (fun ω => A.base r c+a ω*A.alpha r c+1/s ω*A.reciprocal r c) := by
    fun_prop
  exact hc.mul (hh c)

theorem measurable_scheduled_head_score {d ℓ : ℕ} (A : ScheduledHead d) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin ℓ → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q k : Fin ℓ) :
    Measurable (fun ω => ∑ p, (A.query.eval (a ω) (s ω)).mulVec (H ω q) p*(A.key.eval (a ω) (s ω)).mulVec (H ω k) p) :=
  Finset.measurable_sum _ (fun p _ =>
    (measurable_scheduled_matrix_action _ a s ha hs _ (hH q) p).mul (measurable_scheduled_matrix_action _ a s ha hs _ (hH k) p))

theorem measurable_scheduled_relu_head {d ℓ : ℕ} (A : ScheduledHead d) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin ℓ → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin ℓ) (r : Fin d) : Measurable (fun ω => A.relu (a ω) (s ω) (H ω) q r) := by
  unfold ScheduledHead.relu matrixReLUHead
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_const.max (measurable_scheduled_head_score A a s ha hs H hH q k)).mul
      (measurable_scheduled_matrix_action _ a s ha hs _ (hH k) r))

theorem measurable_scheduled_softmax_head {d n : ℕ} (A : ScheduledHead d) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin (n+1) → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin (n+1)) (r : Fin d) : Measurable (fun ω => A.maskedSoftmax (a ω) (s ω) (H ω) q r) := by
  unfold ScheduledHead.maskedSoftmax softmaxReadout
  apply Measurable.div
  · exact Finset.measurable_sum _ (fun i _ =>
      (measurable_scheduled_matrix_action _ a s ha hs _ (hH i.castSucc) r).mul
        ((Real.continuous_exp.measurable).comp (measurable_scheduled_head_score A a s ha hs H hH q i.castSucc)))
  · exact Finset.measurable_sum _ (fun i _ => (Real.continuous_exp.measurable).comp (measurable_scheduled_head_score A a s ha hs H hH q i.castSucc))

theorem measurable_scheduled_relu_block {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 4) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin (n+1) → Fin (embedWidth D) → ℝ)
    (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    Measurable (fun ω => T.reluBlock k (a ω) (s ω) (H ω) q r) := by
  let Z := fun ω q r => H ω q r+∑ i, (T.reluHeads k i).relu (a ω) (s ω) (H ω) q r
  have hZ (q : Fin (n+1)) (r : Fin (embedWidth D)) : Measurable (fun ω => Z ω q r) :=
    (hH q r).add (Finset.measurable_sum _ (fun i _ => measurable_scheduled_relu_head _ a s ha hs H hH q r))
  exact (hZ q r).add (measurable_six_ffn (T.reluFFN k) _ (hZ q) r)

theorem measurable_scheduled_final_block {n D : ℕ} (T : FiveBlockTransformer n D) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin (n+1) → Fin (embedWidth D) → ℝ)
    (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    Measurable (fun ω => T.finalBlock (a ω) (s ω) (H ω) q r) := by
  let Z := fun ω q r => H ω q r+T.finalHead.maskedSoftmax (a ω) (s ω) (H ω) q r
  have hZ (q : Fin (n+1)) (r : Fin (embedWidth D)) : Measurable (fun ω => Z ω q r) :=
    (hH q r).add (measurable_scheduled_softmax_head _ a s ha hs H hH q r)
  exact (hZ q r).add (measurable_six_ffn T.finalFFN _ (hZ q) r)

theorem measurable_scheduled_transformer_eval {n D : ℕ} (T : FiveBlockTransformer n D) (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (x : Ω → Fin n → Fin D → ℝ) (y : Ω → Fin D → ℝ)
    (hx : ∀ i j, Measurable (fun ω => x ω i j)) (hy : ∀ j, Measurable (fun ω => y ω j)) :
    Measurable (fun ω => T.eval (a ω) (s ω) (x ω) (y ω)) := by
  have h0 := measurable_initial_embedding n D x y hx hy
  have h1 := measurable_scheduled_relu_block T 0 a s ha hs _ h0
  have h2 := measurable_scheduled_relu_block T 1 a s ha hs _ h1
  have h3 := measurable_scheduled_relu_block T 2 a s ha hs _ h2
  have h4 := measurable_scheduled_relu_block T 3 a s ha hs _ h3
  exact measurable_scheduled_final_block T a s ha hs _ h4 (Fin.last n) (valueFlat D)

#print axioms measurable_scheduled_matrix_action
#print axioms measurable_scheduled_head_score
#print axioms measurable_scheduled_relu_head
#print axioms measurable_scheduled_softmax_head
#print axioms measurable_scheduled_relu_block
#print axioms measurable_scheduled_final_block
#print axioms measurable_scheduled_transformer_eval
end GeneralizationCheck
