module

public import ICLGeneralization.TransformerNetwork
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open MeasureTheory Matrix
namespace GeneralizationCheck

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_matrix_action {d e : ℕ} (A : Matrix (Fin d) (Fin e) ℝ)
    (h : Ω → Fin e → ℝ) (hh : ∀ r, Measurable (fun ω => h ω r)) (r : Fin d) :
    Measurable (fun ω => A.mulVec (h ω) r) := by
  unfold Matrix.mulVec dotProduct
  exact Finset.measurable_sum _ (fun c _ => (hh c).const_mul _)

theorem measurable_six_ffn {d w : ℕ} (F : SixLayerFFN d w) (h : Ω → Fin d → ℝ)
    (hh : ∀ r, Measurable (fun ω => h ω r)) (r : Fin d) :
    Measurable (fun ω => F.eval (h ω) r) := by
  let first := fun ω p => max 0 (F.input.mulVec (h ω) p+F.inputBias p)
  let step := fun v p => max 0 (F.hidden.mulVec v p+F.hiddenBias p)
  have hf (p : Fin w) : Measurable (fun ω => first ω p) :=
    measurable_const.max ((measurable_matrix_action F.input h hh p).add_const _)
  have hi (k : ℕ) : ∀ p, Measurable (fun ω => (step^[k]) (first ω) p) := by
    induction k with
    | zero => exact hf
    | succ k ih =>
      intro p
      simp only [Function.iterate_succ_apply']
      exact measurable_const.max ((measurable_matrix_action F.hidden _ ih p).add_const _)
  exact (measurable_matrix_action F.output _ (hi 4) r).add_const _

theorem measurable_head_score {d ℓ : ℕ} (A : ScheduledHead d) (a s : ℝ)
    (H : Ω → Fin ℓ → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q k : Fin ℓ) :
    Measurable (fun ω => ∑ p, (A.query.eval a s).mulVec (H ω q) p*(A.key.eval a s).mulVec (H ω k) p) :=
  Finset.measurable_sum _ (fun p _ =>
    (measurable_matrix_action _ _ (hH q) p).mul (measurable_matrix_action _ _ (hH k) p))

theorem measurable_relu_head {d ℓ : ℕ} (A : ScheduledHead d) (a s : ℝ)
    (H : Ω → Fin ℓ → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin ℓ) (r : Fin d) : Measurable (fun ω => A.relu a s (H ω) q r) := by
  unfold ScheduledHead.relu matrixReLUHead
  exact Finset.measurable_sum _ (fun k _ =>
    (measurable_const.max (measurable_head_score A a s H hH q k)).mul
      (measurable_matrix_action _ _ (hH k) r))

theorem measurable_softmax_head {d n : ℕ} (A : ScheduledHead d) (a s : ℝ)
    (H : Ω → Fin (n+1) → Fin d → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin (n+1)) (r : Fin d) : Measurable (fun ω => A.maskedSoftmax a s (H ω) q r) := by
  unfold ScheduledHead.maskedSoftmax softmaxReadout
  apply Measurable.div
  · exact Finset.measurable_sum _ (fun i _ =>
      (measurable_matrix_action _ _ (hH i.castSucc) r).mul
        ((Real.continuous_exp.measurable).comp (measurable_head_score A a s H hH q i.castSucc)))
  · exact Finset.measurable_sum _ (fun i _ => (Real.continuous_exp.measurable).comp (measurable_head_score A a s H hH q i.castSucc))

theorem measurable_relu_block {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 4) (a s : ℝ)
    (H : Ω → Fin (n+1) → Fin (embedWidth D) → ℝ)
    (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    Measurable (fun ω => T.reluBlock k a s (H ω) q r) := by
  let Z := fun ω q r => H ω q r+∑ i, (T.reluHeads k i).relu a s (H ω) q r
  have hZ (q : Fin (n+1)) (r : Fin (embedWidth D)) : Measurable (fun ω => Z ω q r) :=
    (hH q r).add (Finset.measurable_sum _ (fun i _ => measurable_relu_head _ a s H hH q r))
  exact (hZ q r).add (measurable_six_ffn (T.reluFFN k) _ (hZ q) r)

theorem measurable_final_block {n D : ℕ} (T : FiveBlockTransformer n D) (a s : ℝ)
    (H : Ω → Fin (n+1) → Fin (embedWidth D) → ℝ)
    (hH : ∀ q r, Measurable (fun ω => H ω q r)) (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    Measurable (fun ω => T.finalBlock a s (H ω) q r) := by
  let Z := fun ω q r => H ω q r+T.finalHead.maskedSoftmax a s (H ω) q r
  have hZ (q : Fin (n+1)) (r : Fin (embedWidth D)) : Measurable (fun ω => Z ω q r) :=
    (hH q r).add (measurable_softmax_head _ a s H hH q r)
  exact (hZ q r).add (measurable_six_ffn T.finalFFN _ (hZ q) r)

theorem measurable_initial_embedding (n D : ℕ) (x : Ω → Fin n → Fin D → ℝ) (y : Ω → Fin D → ℝ)
    (hx : ∀ i j, Measurable (fun ω => x ω i j)) (hy : ∀ j, Measurable (fun ω => y ω j))
    (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    Measurable (fun ω => packState (initialState n D (x ω) (y ω)) q r) := by
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp only [packState, packCore, Fin.addCases_left, initialState]
        split_ifs
        · exact hx _ r
        · exact hy r
      · simp only [packState, packCore, Fin.addCases_left, Fin.addCases_right, initialState]
        exact measurable_const
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp only [packState, packCore, Fin.addCases_left, Fin.addCases_right, initialState]
        exact measurable_const
      · fin_cases r <;> simp only [packState, packCore, Fin.addCases_left, Fin.addCases_right, initialState]
        all_goals exact measurable_const
  · simp only [packState, Fin.addCases_right]
    exact measurable_const

theorem measurable_transformer_eval {n D : ℕ} (T : FiveBlockTransformer n D) (a s : ℝ)
    (x : Ω → Fin n → Fin D → ℝ) (y : Ω → Fin D → ℝ)
    (hx : ∀ i j, Measurable (fun ω => x ω i j)) (hy : ∀ j, Measurable (fun ω => y ω j)) :
    Measurable (fun ω => T.eval a s (x ω) (y ω)) := by
  have h0 := measurable_initial_embedding n D x y hx hy
  have h1 := measurable_relu_block T 0 a s _ h0
  have h2 := measurable_relu_block T 1 a s _ h1
  have h3 := measurable_relu_block T 2 a s _ h2
  have h4 := measurable_relu_block T 3 a s _ h3
  exact measurable_final_block T a s _ h4 (Fin.last n) (valueFlat D)

#print axioms measurable_matrix_action
#print axioms measurable_six_ffn
#print axioms measurable_head_score
#print axioms measurable_relu_head
#print axioms measurable_softmax_head
#print axioms measurable_relu_block
#print axioms measurable_final_block
#print axioms measurable_initial_embedding
#print axioms measurable_transformer_eval
end GeneralizationCheck
