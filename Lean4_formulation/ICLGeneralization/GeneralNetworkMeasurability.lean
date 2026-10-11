module

public import ICLGeneralization.GeneralLossStability
public import ICLGeneralization.ScheduledNetworkMeasurability
public import ICLGeneralization.TaskSamplingKernel

@[expose] public section
open MeasureTheory
namespace GeneralizationCheck
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_general_ffn {D w L F m : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (activation : Fin F → Bool) (x : Ω → Fin w → ℝ)
    (hx : ∀ r, Measurable (fun ω => x ω r)) (j : ℕ) (hj : j ≤ F) :
    ∀ r, Measurable (fun ω => generalFFNState θ k activation (x ω) j r) := by
  induction j with
  | zero => exact hx
  | succ j ih =>
    have hj' : j < F := by omega
    have hi := ih (by omega)
    intro r
    simp only [generalFFNState,dite_eq_left hj']
    have hm := (measurable_matrix_action (generalAffineMatrix θ k ⟨j,hj'⟩)
      (fun ω => generalFFNState θ k activation (x ω) j) hi r).add_const
      (generalAffineBias θ k ⟨j,hj'⟩ r)
    cases hh : activation ⟨j,hj'⟩
    · simpa [generalAffine,hh] using hm
    · simpa [generalAffine,hh] using measurable_const.max hm

theorem measurable_general_mha {D w L F m ℓ n : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (softmax : Bool) (mask : Fin n → Fin ℓ)
    (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin ℓ → Fin w → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin ℓ) (r : Fin w) : Measurable (fun ω => generalMHA θ k softmax mask (a ω) (s ω) (H ω) q r) := by
  unfold generalMHA
  apply Finset.measurable_sum
  intro i _
  cases softmax
  · exact measurable_scheduled_relu_head (generalHead θ k i) a s ha hs H hH q r
  · unfold maskedMatrixHead softmaxReadout attentionScore
    apply Measurable.div
    · apply Finset.measurable_sum
      intro j _
      exact (measurable_scheduled_matrix_action (generalHead θ k i).value a s ha hs _ (hH (mask j)) r).mul
        (Real.continuous_exp.measurable.comp (measurable_scheduled_head_score (generalHead θ k i) a s ha hs H hH q (mask j)))
    · exact Finset.measurable_sum _ (fun j _ => Real.continuous_exp.measurable.comp
        (measurable_scheduled_head_score (generalHead θ k i) a s ha hs H hH q (mask j)))

theorem measurable_general_block {D w L F m ℓ n : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (k : Fin L) (softmax : Bool) (activation : Fin F → Bool) (mask : Fin n → Fin ℓ)
    (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s)
    (H : Ω → Fin ℓ → Fin w → ℝ) (hH : ∀ q r, Measurable (fun ω => H ω q r))
    (q : Fin ℓ) (r : Fin w) : Measurable (fun ω => generalBlock θ k softmax activation mask (a ω) (s ω) (H ω) q r) := by
  let Z := fun ω q r => H ω q r+generalMHA θ k softmax mask (a ω) (s ω) (H ω) q r
  have hz (q : Fin ℓ) (r : Fin w) : Measurable (fun ω => Z ω q r) :=
    (hH q r).add (measurable_general_mha θ k softmax mask a s ha hs H hH q r)
  exact (hz q r).add (measurable_general_ffn θ k activation (fun ω => Z ω q) (hz q) F (le_refl _) r)

theorem measurable_general_transformer {D w L F m ℓ n : ℕ} (θ : GeneralParameter D w L F m → ℝ)
    (PE tokenMask : Fin ℓ → Fin w → ℝ) (x : Ω → Fin ℓ → Fin D → ℝ)
    (hx : ∀ q r, Measurable (fun ω => x ω q r)) (softmax : Fin L → Bool)
    (activation : Fin L → Fin F → Bool) (mask : Fin n → Fin ℓ)
    (a s : Ω → ℝ) (ha : Measurable a) (hs : Measurable s) (q : Fin ℓ) :
    Measurable (fun ω => generalTransformer θ PE tokenMask (x ω) softmax activation mask (a ω) (s ω) q) := by
  have hi (j : ℕ) (hj : j ≤ L) : ∀ q r, Measurable (fun ω => generalState θ PE tokenMask (x ω)
      softmax activation mask (a ω) (s ω) j q r) := by
    induction j with
    | zero =>
      intro q r
      unfold generalState generalEmbedding
      exact measurable_const.add ((Finset.measurable_sum _ (fun c _ => (hx q c).const_mul _)).const_mul _)
    | succ j ih =>
      have hj' : j < L := by omega
      intro q r
      simp only [generalState,dite_eq_left hj']
      exact measurable_general_block θ ⟨j,hj'⟩ _ _ mask a s ha hs _ (ih (by omega)) q r
  exact Finset.measurable_sum _ (fun r _ => (hi L (le_refl _) q r).const_mul _)

theorem measurable_restricted_general_loss {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (θ : VectorGeneralParameter D w L F m → ℝ)
    (hx : ∀ q r, Measurable (fun ω => S.input ω q r)) (ha : Measurable S.alpha) (hs : Measurable S.sigma)
    (hz : ∀ j, Measurable (fun ω => S.clean ω j)) (hA : MeasurableSet S.event) :
    Measurable (restrictedGeneralLoss S θ) := by
  have hg (j : Fin D) : Measurable (fun ω => generalMean S θ ω j) :=
    measurable_general_transformer (fun p => θ (j,p)) S.PE S.tokenMask S.input hx
      S.softmax S.activation S.mask S.alpha S.sigma ha hs S.readToken
  have hf : Measurable (fun ω => meanSquaredLoss D (S.alpha ω) (S.sigma ω) (generalMean S θ ω) (S.clean ω)) :=
    ((ha.pow_const 2).div (hs.pow_const 4)).mul (Finset.measurable_sum _ (fun j _ => ((hg j).sub (hz j)).pow_const 2))
  exact hf.ite hA measurable_const

#print axioms measurable_general_ffn
#print axioms measurable_general_mha
#print axioms measurable_general_block
#print axioms measurable_general_transformer
#print axioms measurable_restricted_general_loss
end GeneralizationCheck
