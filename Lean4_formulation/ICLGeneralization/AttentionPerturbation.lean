module

public import ICLGeneralization.NetworkPerturbation
public import ICLGeneralization.TransformerNetwork

@[expose] public section
open Matrix
namespace GeneralizationCheck

noncomputable def attentionScore {d ℓ : ℕ} (Q K : Matrix (Fin d) (Fin d) ℝ)
    (H : Fin ℓ → Fin d → ℝ) (q k : Fin ℓ) : ℝ :=
  ∑ p, Q.mulVec (H q) p*K.mulVec (H k) p

theorem attention_score_bound {d ℓ : ℕ} (Q K : Matrix (Fin d) (Fin d) ℝ)
    (H : Fin ℓ → Fin d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hQ : ∀ q p, |Q.mulVec (H q) p| ≤ B) (hK : ∀ q p, |K.mulVec (H q) p| ≤ B)
    (q k : Fin ℓ) : |attentionScore Q K H q k| ≤ (d : ℝ)*B^2 := by
  exact (finite_sum_abs_bound d _ (B*B)
    (fun p => by rw [abs_mul]; exact mul_le_mul (hQ q p) (hK k p) (abs_nonneg _) hB)).trans_eq (by ring)

theorem attention_score_perturbation {d ℓ : ℕ} (Q K Q' K' : Matrix (Fin d) (Fin d) ℝ)
    (H H' : Fin ℓ → Fin d → ℝ) (B E : ℝ) (hB : 0 ≤ B)
    (hQ' : ∀ q p, |Q'.mulVec (H' q) p| ≤ B) (hK : ∀ q p, |K.mulVec (H q) p| ≤ B)
    (hQ : ∀ q p, |Q.mulVec (H q) p-Q'.mulVec (H' q) p| ≤ E)
    (hK' : ∀ q p, |K.mulVec (H q) p-K'.mulVec (H' q) p| ≤ E)
    (q k : Fin ℓ) : |attentionScore Q K H q k-attentionScore Q' K' H' q k| ≤ 2*(d : ℝ)*B*E := by
  unfold attentionScore
  rw [← Finset.sum_sub_distrib]
  exact (finite_sum_abs_bound d _ (E*B+B*E)
    (fun p => product_perturbation _ _ _ _ B B E E hB (hQ' q p) (hK k p) (hQ q p) (hK' k p))).trans_eq (by ring)

theorem relu_attention_bound {d ℓ : ℕ} (Q K V : Matrix (Fin d) (Fin d) ℝ)
    (H : Fin ℓ → Fin d → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hQ : ∀ q p, |Q.mulVec (H q) p| ≤ B) (hK : ∀ q p, |K.mulVec (H q) p| ≤ B)
    (hV : ∀ q p, |V.mulVec (H q) p| ≤ B) (q : Fin ℓ) (r : Fin d) :
    |matrixReLUHead Q K V H q r| ≤ (ℓ : ℝ)*(d : ℝ)*B^3 := by
  unfold matrixReLUHead
  have h := finite_sum_abs_bound ℓ _ ((d : ℝ)*B^2*B) (fun k => by
    rw [abs_mul]
    exact mul_le_mul (relu_abs_bound _ _ (by positivity) (attention_score_bound Q K H B hB hQ hK q k))
      (hV k r) (abs_nonneg _) (by positivity))
  exact h.trans_eq (by ring)

theorem relu_attention_perturbation {d ℓ : ℕ} (Q K V Q' K' V' : Matrix (Fin d) (Fin d) ℝ)
    (H H' : Fin ℓ → Fin d → ℝ) (B E : ℝ) (hB : 0 ≤ B) (_hE : 0 ≤ E)
    (hQ : ∀ q p, |Q.mulVec (H q) p| ≤ B) (hQ' : ∀ q p, |Q'.mulVec (H' q) p| ≤ B)
    (hK : ∀ q p, |K.mulVec (H q) p| ≤ B) (hK' : ∀ q p, |K'.mulVec (H' q) p| ≤ B)
    (hV : ∀ q p, |V.mulVec (H q) p| ≤ B) (_hV' : ∀ q p, |V'.mulVec (H' q) p| ≤ B)
    (hQdiff : ∀ q p, |Q.mulVec (H q) p-Q'.mulVec (H' q) p| ≤ E)
    (hKdiff : ∀ q p, |K.mulVec (H q) p-K'.mulVec (H' q) p| ≤ E)
    (hVdiff : ∀ q p, |V.mulVec (H q) p-V'.mulVec (H' q) p| ≤ E)
    (q : Fin ℓ) (r : Fin d) :
    |matrixReLUHead Q K V H q r-matrixReLUHead Q' K' V' H' q r| ≤ 3*(ℓ : ℝ)*(d : ℝ)*B^2*E := by
  unfold matrixReLUHead
  rw [← Finset.sum_sub_distrib]
  have hs := attention_score_bound Q K H B hB hQ hK
  have hs' := attention_score_bound Q' K' H' B hB hQ' hK'
  have hdiff := attention_score_perturbation Q K Q' K' H H' B E hB hQ' hK hQdiff hKdiff
  have h := finite_sum_abs_bound ℓ _ (2*(d : ℝ)*B*E*B+((d : ℝ)*B^2)*E)
    (fun k => product_perturbation _ _ _ _ ((d : ℝ)*B^2) B (2*(d : ℝ)*B*E) E
      (by positivity) (relu_abs_bound _ _ (by positivity) (hs' q k)) (hV k r)
      (relu_perturbation _ _ _ (hdiff q k)) (hVdiff k r))
  exact h.trans_eq (by ring)

noncomputable def maskedMatrixHead {d ℓ n : ℕ} (Q K V : Matrix (Fin d) (Fin d) ℝ)
    (mask : Fin n → Fin ℓ) (H : Fin ℓ → Fin d → ℝ) (q : Fin ℓ) (r : Fin d) : ℝ :=
  softmaxReadout n (fun i => attentionScore Q K H q (mask i)) (fun i => V.mulVec (H (mask i)) r)

theorem softmax_attention_bound {d ℓ n : ℕ} (hn : 0 < n)
    (Q K V : Matrix (Fin d) (Fin d) ℝ) (mask : Fin n → Fin ℓ)
    (H : Fin ℓ → Fin d → ℝ) (B : ℝ) (hV : ∀ q p, |V.mulVec (H q) p| ≤ B)
    (q : Fin ℓ) (r : Fin d) : |maskedMatrixHead Q K V mask H q r| ≤ B :=
  softmax_abs_bound n hn _ _ B (fun i => hV (mask i) r)

theorem softmax_attention_perturbation {d ℓ n : ℕ} (hn : 0 < n)
    (Q K V Q' K' V' : Matrix (Fin d) (Fin d) ℝ) (mask : Fin n → Fin ℓ)
    (H H' : Fin ℓ → Fin d → ℝ) (B E : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hQ' : ∀ q p, |Q'.mulVec (H' q) p| ≤ B) (hK : ∀ q p, |K.mulVec (H q) p| ≤ B)
    (hV : ∀ q p, |V.mulVec (H q) p| ≤ B)
    (hQdiff : ∀ q p, |Q.mulVec (H q) p-Q'.mulVec (H' q) p| ≤ E)
    (hKdiff : ∀ q p, |K.mulVec (H q) p-K'.mulVec (H' q) p| ≤ E)
    (hVdiff : ∀ q p, |V.mulVec (H q) p-V'.mulVec (H' q) p| ≤ E)
    (q : Fin ℓ) (r : Fin d) :
    |maskedMatrixHead Q K V mask H q r-maskedMatrixHead Q' K' V' mask H' q r| ≤ (1+4*(d : ℝ)*B^2)*E := by
  have h := softmax_joint_stability n hn _ _ _ _ B (2*(d : ℝ)*B*E) E hB (by positivity)
    (fun i => hV (mask i) r)
    (fun i => attention_score_perturbation Q K Q' K' H H' B E hB hQ' hK hQdiff hKdiff q (mask i))
    (fun i => hVdiff (mask i) r)
  exact h.trans_eq (by ring)

#print axioms attention_score_bound
#print axioms attention_score_perturbation
#print axioms relu_attention_bound
#print axioms relu_attention_perturbation
#print axioms softmax_attention_bound
#print axioms softmax_attention_perturbation
end GeneralizationCheck
