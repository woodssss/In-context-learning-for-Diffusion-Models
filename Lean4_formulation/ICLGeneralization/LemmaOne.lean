module

public import ICLGeneralization.NetworkBudget

@[expose] public section

namespace GeneralizationCheck

/- Membership for the concrete five-block architecture defined in
   TransformerNetwork: fixed shared matrix coefficients, n heads in the first
   four blocks, one head in the last, six affine FFN layers, and bounded output.
   Fixed time operations and the prompt-only mask match the paper's convention. -/
def InScalarTransformerClass {n D : ℕ} (T : FiveBlockTransformer n D) (R κ : ℝ) : Prop :=
  T.Bounded κ ∧ ∀ (a s : ℝ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ), |T.eval a s x y| ≤ R

noncomputable def lemmaOneBudget (n D : ℕ) (M : ℝ) : ℝ :=
  10*(D : ℝ)^4*(n+1 : ℝ)^2*M^4

theorem kernel_transformer_in_scalar_class (n D : ℕ) (hD : 1 ≤ D) (j : Fin D)
    (b R s0 C : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) :
    InScalarTransformerClass (kernelTransformer n D j (realizationM D b R s0 C) b)
      R (lemmaOneBudget n D (realizationM D b R s0 C)) := by
  let M := realizationM D b R s0 C
  have hM : 1 ≤ M := realization_M_at_least_one D b R s0 C
  have hbM : |b| ≤ M := by
    rw [abs_of_nonneg (by linarith : 0 ≤ b)]
    exact realization_M_at_least_support D b R s0 C hR
  constructor
  · apply network_budget_mono _ (intermediateBudget n M) _
      (kernel_transformer_bounded n D j M b hM hbM)
    have h := advertised_coefficient_budget D (n+1) hD M hM
    simpa only [intermediateBudget, lemmaOneBudget, Nat.cast_add, Nat.cast_one] using h
  · intro a s x y
    have h := kernel_transformer_global_bound n D j M b a s (by linarith) x y
    exact (abs_le.mpr h).trans hR

/- The existential quantifier precedes all prompt, query, and schedule inputs.
   The witness is an actual collection of Q/K/V and FFN matrix records. -/
theorem lemma_one_transformer_realization (n D : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (b R C s0 : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (_hC : 0 ≤ C) (hs0 : 0 < s0) :
    ∃ G : Fin D → FiveBlockTransformer n D,
      (embedWidth D = 2*D+6 ∧ hiddenWidth D = 2*D+6 ∧ 1 ≤ n) ∧
      (∀ j, InScalarTransformerClass (G j) R (lemmaOneBudget n D (realizationM D b R s0 C))) ∧
      (∀ (a s : ℝ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) (j : Fin D),
        -b ≤ (G j).eval a s x y ∧ (G j).eval a s x y ≤ b) ∧
      (∀ (a s : ℝ), (0 ≤ a ∧ a ≤ 1) → s0 ≤ s →
        ∀ (x : Fin n → EuclideanSpace ℝ (Fin D)) (z eps : EuclideanSpace ℝ (Fin D)),
          (∀ i r, -b ≤ x i r ∧ x i r ≤ b) →
          (∀ r, -b ≤ z r ∧ z r ≤ b) → ‖eps‖ ≤ C →
          (fun j => (G j).eval a s (fun i r => x i r) (fun r => (a • z+s • eps) r)) =
          (fun j => softmaxReadout n
            (fun i => -(∑ r, ((a • z+s • eps) r-a*x i r)^2)/(2*s^2)) (fun i => x i j))) := by
  refine ⟨fun j => kernelTransformer n D j (realizationM D b R s0 C) b,
    ⟨flat_embedding_dimension D, network_hidden_dimension D, hn⟩, ?_, ?_, ?_⟩
  · intro j
    exact kernel_transformer_in_scalar_class n D hD j b R s0 C hb hR
  · intro a s x y j
    exact kernel_transformer_global_bound n D j _ b a s (by linarith) x y
  · intro a s ha hs x z eps hx hz heps
    funext j
    exact kernel_transformer_exact n D hn j b R C a s s0 (by linarith) ha hs0 hs
      x z eps hx hz heps

#print axioms kernel_transformer_in_scalar_class
#print axioms lemma_one_transformer_realization
end GeneralizationCheck
