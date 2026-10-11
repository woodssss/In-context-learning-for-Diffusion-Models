module

public import ICLGeneralization.AttentionPerturbation

@[expose] public section
open Matrix
namespace GeneralizationCheck

/- Full parameter families, rather than the particular kernel witness. The
   three prescribed schedule components are independent shared records. -/
abbrev GeneralParameter (D w L F m : ℕ) :=
  (Fin w × Fin D) ⊕ ((Fin L × Fin m × Fin 3 × Fin 3 × Fin w × Fin w) ⊕
    ((Fin L × Fin F × ((Fin w × Fin w) ⊕ Fin w)) ⊕ Fin w))

noncomputable def generalParameterCount (D w L F m : ℕ) : ℕ :=
  w*D+L*(9*m*w^2+F*(w^2+w))+w

theorem general_parameter_count (D w L F m : ℕ) :
    Fintype.card (GeneralParameter D w L F m) = generalParameterCount D w L F m := by
  simp only [GeneralParameter,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,generalParameterCount]
  ring

noncomputable def generalScheduledMatrix {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (i : Fin m) (h : Fin 3) : ScheduledMatrix w where
  base r c := θ (.inr (.inl (k,i,h,0,r,c)))
  alpha r c := θ (.inr (.inl (k,i,h,1,r,c)))
  reciprocal r c := θ (.inr (.inl (k,i,h,2,r,c)))

noncomputable def generalHead {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (i : Fin m) : ScheduledHead w :=
  ⟨generalScheduledMatrix θ k i 0, generalScheduledMatrix θ k i 1, generalScheduledMatrix θ k i 2⟩

noncomputable def generalAffineMatrix {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (j : Fin F) : Matrix (Fin w) (Fin w) ℝ :=
  fun r c => θ (.inr (.inr (.inl (k,j,.inl (r,c)))))

noncomputable def generalAffineBias {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (j : Fin F) : Fin w → ℝ :=
  fun r => θ (.inr (.inr (.inl (k,j,.inr r))))

noncomputable def generalAffine {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (j : Fin F)
    (relu : Bool) (x : Fin w → ℝ) : Fin w → ℝ := fun r =>
  let z := (generalAffineMatrix θ k j).mulVec x r+generalAffineBias θ k j r
  if relu then max 0 z else z

noncomputable def generalFFNState {D w L F m : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (activation : Fin F → Bool)
    (x : Fin w → ℝ) : ℕ → Fin w → ℝ
  | 0 => x
  | j+1 => if hj : j < F then generalAffine θ k ⟨j,hj⟩ (activation ⟨j,hj⟩)
      (generalFFNState θ k activation x j) else generalFFNState θ k activation x j

noncomputable def generalMHA {D w L F m ℓ n : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool)
    (mask : Fin n → Fin ℓ) (a s : ℝ) (H : Fin ℓ → Fin w → ℝ) : Fin ℓ → Fin w → ℝ :=
  fun q r => ∑ i, if softmax then maskedMatrixHead
    ((generalHead θ k i).query.eval a s) ((generalHead θ k i).key.eval a s)
    ((generalHead θ k i).value.eval a s) mask H q r
    else (generalHead θ k i).relu a s H q r

noncomputable def generalBlock {D w L F m ℓ n : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (k : Fin L) (softmax : Bool)
    (activation : Fin F → Bool) (mask : Fin n → Fin ℓ) (a s : ℝ)
    (H : Fin ℓ → Fin w → ℝ) : Fin ℓ → Fin w → ℝ :=
  let Z := fun q r => H q r+generalMHA θ k softmax mask a s H q r
  fun q r => Z q r+generalFFNState θ k activation (Z q) F r

noncomputable def generalEmbedding {D w L F m ℓ : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) : Fin ℓ → Fin w → ℝ :=
  fun q r => PE q r+tokenMask q r*∑ c, θ (.inl (r,c))*x q c

noncomputable def generalState {D w L F m ℓ n : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) (softmax : Fin L → Bool)
    (activation : Fin L → Fin F → Bool) (mask : Fin n → Fin ℓ) (a s : ℝ) : ℕ → Fin ℓ → Fin w → ℝ
  | 0 => generalEmbedding θ PE tokenMask x
  | k+1 => if hk : k < L then generalBlock θ ⟨k,hk⟩ (softmax ⟨k,hk⟩)
      (activation ⟨k,hk⟩) mask a s (generalState θ PE tokenMask x softmax activation mask a s k)
      else generalState θ PE tokenMask x softmax activation mask a s k

noncomputable def generalTransformer {D w L F m ℓ n : ℕ}
    (θ : GeneralParameter D w L F m → ℝ) (PE tokenMask : Fin ℓ → Fin w → ℝ)
    (x : Fin ℓ → Fin D → ℝ) (softmax : Fin L → Bool)
    (activation : Fin L → Fin F → Bool) (mask : Fin n → Fin ℓ) (a s : ℝ) (q : Fin ℓ) : ℝ :=
  ∑ r, θ (.inr (.inr (.inr r)))*generalState θ PE tokenMask x softmax activation mask a s L q r

#print axioms general_parameter_count
end GeneralizationCheck
