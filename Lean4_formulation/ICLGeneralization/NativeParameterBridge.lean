module

public import ICLGeneralization.LemmaFourFixedTime

@[expose] public section
open Matrix
namespace GeneralizationCheck

noncomputable def castSixFFN {d h w : ℕ} (e : h=w) (F : SixLayerFFN d h) : SixLayerFFN d w := e ▸ F

theorem cast_six_ffn_eval {d h w : ℕ} (e : h=w) (F : SixLayerFFN d h) (x : Fin d → ℝ) :
    (castSixFFN e F).eval x = F.eval x := by cases e; rfl

theorem cast_six_ffn_bounded {d h w : ℕ} (e : h=w) (F : SixLayerFFN d h) (κ : ℝ)
    (hF : F.Bounded κ) : (castSixFFN e F).Bounded κ := by cases e; exact hF

noncomputable def zeroScheduledHead (w : ℕ) : ScheduledHead w :=
  ⟨fixedMatrix 0,fixedMatrix 0,fixedMatrix 0⟩

noncomputable def nativeHead {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (i : Fin n) :
    ScheduledHead (embedWidth D) :=
  if h : k.val < 4 then T.reluHeads ⟨k.val,h⟩ i else if i.val=0 then T.finalHead else zeroScheduledHead _

noncomputable def nativeFFN {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) :
    SixLayerFFN (embedWidth D) (embedWidth D) :=
  castSixFFN ((network_hidden_dimension D).trans (flat_embedding_dimension D).symm)
    (if h : k.val < 4 then T.reluFFN ⟨k.val,h⟩ else T.finalFFN)

noncomputable def nativeMatrixKind {w : ℕ} (H : ScheduledHead w) (h : Fin 3) : ScheduledMatrix w :=
  ![H.query,H.key,H.value] h

noncomputable def nativeLayout {n D : ℕ} (T : FiveBlockTransformer n D) : FixedTimeLayout (embedWidth D) 5 n where
  alpha k i h := (nativeMatrixKind (nativeHead T k i) h).alpha
  reciprocal k i h := (nativeMatrixKind (nativeHead T k i) h).reciprocal

noncomputable def nativeAffine {w : ℕ} (F : SixLayerFFN w w) (j : Fin 6) : Matrix (Fin w) (Fin w) ℝ :=
  if j.val=0 then F.input else if j.val=5 then F.output else F.hidden
noncomputable def nativeBias {w : ℕ} (F : SixLayerFFN w w) (j : Fin 6) : Fin w → ℝ :=
  if j.val=0 then F.inputBias else if j.val=5 then F.outputBias else F.hiddenBias

noncomputable def nativeParameter {n D : ℕ} (T : FiveBlockTransformer n D) :
    FixedTimeParameter D (embedWidth D) 5 6 n → ℝ
  | .inl (r,c) => readRow (cleanFlat c) r
  | .inr (.inl (k,i,h,r,c)) => (nativeMatrixKind (nativeHead T k i) h).base r c
  | .inr (.inr (.inl (k,j,.inl (r,c)))) => nativeAffine (nativeFFN T k) j r c
  | .inr (.inr (.inl (k,j,.inr r))) => nativeBias (nativeFFN T k) j r
  | .inr (.inr (.inr r)) => readRow (valueFlat D) r

noncomputable def nativeLift {n D : ℕ} (T : FiveBlockTransformer n D) := fixedTimeLift (nativeLayout T) (nativeParameter T)
def nativeSoftmax (k : Fin 5) : Bool := decide (k.val=4)
def nativeActivation (_k : Fin 5) (j : Fin 6) : Bool := decide (j.val<5)

noncomputable def nativePE (n D : ℕ) : Fin (n+1) → Fin (embedWidth D) → ℝ :=
  packState (initialState n D (fun _ _ => 0) (fun _ => 0))
noncomputable def nativeRawInput {n D : ℕ} (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :=
  (initialState n D x y).data

theorem native_scheduled_matrix {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (i : Fin n) (h : Fin 3) :
    generalScheduledMatrix (nativeLift T) k i h = nativeMatrixKind (nativeHead T k i) h := by
  simp [nativeLift,generalScheduledMatrix,fixedTimeLift,nativeParameter,nativeLayout]

theorem native_general_head {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (i : Fin n) :
    generalHead (nativeLift T) k i = nativeHead T k i := by
  simp [generalHead,native_scheduled_matrix,nativeMatrixKind]

theorem native_affine_matrix {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (j : Fin 6) :
    generalAffineMatrix (nativeLift T) k j = nativeAffine (nativeFFN T k) j := by funext r c; rfl

theorem native_affine_bias {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (j : Fin 6) :
    generalAffineBias (nativeLift T) k j = nativeBias (nativeFFN T k) j := by funext r; rfl

theorem native_affine_step {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (j : Fin 6)
    (x : Fin (embedWidth D) → ℝ) :
    generalAffine (nativeLift T) k j (nativeActivation k j) x =
    fun r => if j.val<5 then max 0 ((nativeAffine (nativeFFN T k) j).mulVec x r+nativeBias (nativeFFN T k) j r)
      else (nativeAffine (nativeFFN T k) j).mulVec x r+nativeBias (nativeFFN T k) j r := by
  funext r
  simp [generalAffine,native_affine_matrix,native_affine_bias,nativeActivation]

theorem native_general_ffn {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 5) (x : Fin (embedWidth D) → ℝ) :
    generalFFNState (nativeLift T) k (nativeActivation k) x 6 = (nativeFFN T k).eval x := by
  have hstep (j : ℕ) (hj : j<6) :
      generalFFNState (nativeLift T) k (nativeActivation k) x (j+1) =
      generalAffine (nativeLift T) k ⟨j,hj⟩ (nativeActivation k ⟨j,hj⟩)
        (generalFFNState (nativeLift T) k (nativeActivation k) x j) := by
    rw [generalFFNState,dite_eq_left hj]
  rw [hstep 5 (by decide),hstep 4 (by decide),hstep 3 (by decide),hstep 2 (by decide),
    hstep 1 (by decide),hstep 0 (by decide)]
  simp only [generalFFNState]
  simp only [native_affine_step]
  simp [nativeAffine,nativeBias,SixLayerFFN.eval,Function.iterate_succ_apply]

theorem zero_scheduled_head_masked {w ℓ n : ℕ} (mask : Fin n → Fin ℓ) (a s : ℝ)
    (H : Fin ℓ → Fin w → ℝ) (q : Fin ℓ) (r : Fin w) :
    maskedMatrixHead ((zeroScheduledHead w).query.eval a s) ((zeroScheduledHead w).key.eval a s)
      ((zeroScheduledHead w).value.eval a s) mask H q r = 0 := by
  simp [zeroScheduledHead,fixed_matrix_eval,maskedMatrixHead,softmaxReadout]

theorem native_relu_block {n D : ℕ} (T : FiveBlockTransformer n D) (k : Fin 4) (a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    generalBlock (nativeLift T) k.castSucc (nativeSoftmax k.castSucc) (nativeActivation k.castSucc)
      Fin.castSucc a s H = T.reluBlock k a s H := by
  have hk : k.val ≠ 4 := by omega
  simp [generalBlock,generalMHA,nativeSoftmax,hk,native_general_head,nativeHead,k.isLt,
    native_general_ffn,nativeFFN,cast_six_ffn_eval,FiveBlockTransformer.reluBlock]

theorem native_final_block {n D : ℕ} (hn : 0 < n) (T : FiveBlockTransformer n D) (a s : ℝ)
    (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
    generalBlock (nativeLift T) 4 (nativeSoftmax 4) (nativeActivation 4) Fin.castSucc a s H =
      T.finalBlock a s H := by
  classical
  have hm (q : Fin (n+1)) (r : Fin (embedWidth D)) :
      generalMHA (nativeLift T) 4 true Fin.castSucc a s H q r = T.finalHead.maskedSoftmax a s H q r := by
    simp only [generalMHA,ite_true,native_general_head,nativeHead]
    simp only [show ¬(4:Fin 5).val<4 by decide,dite_false]
    rw [Finset.sum_eq_single (⟨0,hn⟩ : Fin n)]
    · simp [maskedMatrixHead,ScheduledHead.maskedSoftmax,attentionScore]
    · intro i _ hi
      have hv : i.val≠0 := by intro h; apply hi; exact Fin.ext h
      simp only [hv,ite_false]
      exact zero_scheduled_head_masked _ _ _ _ _ _
    · simp
  have hb : nativeSoftmax (4:Fin 5) = true := by decide
  simp only [generalBlock,hb,hm,native_general_ffn,nativeFFN]
  simp only [show ¬(4:Fin 5).val<4 by decide,dite_false,cast_six_ffn_eval]
  rfl

theorem native_embedding {n D : ℕ} (T : FiveBlockTransformer n D)
    (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    generalEmbedding (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y) =
      packState (initialState n D x y) := by
  classical
  funext q r
  simp only [generalEmbedding,nativeLift,fixedTimeLift,nativeParameter,one_mul]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [nativePE,packState,packCore,initialState,nativeRawInput,readRow,cleanFlat,cleanCore]
      · have h (c : Fin D) : Fin.natAdd D r ≠ Fin.castAdd 1 c := by
          intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
        simp [nativePE,packState,packCore,initialState,nativeRawInput,readRow,cleanFlat,cleanCore,h]
    · have h (c : Fin D) : Fin.natAdd (D+1) r ≠ (Fin.castAdd (D+2) (Fin.castAdd 1 c)) := by
        intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd,Fin.val_castAdd] at hv; omega
      simp [nativePE,packState,packCore,initialState,nativeRawInput,readRow,cleanFlat,cleanCore,h]
  · have h (c : Fin D) : Fin.natAdd (coreWidth D) r ≠
        (Fin.castAdd 3 (Fin.castAdd (D+2) (Fin.castAdd 1 c))) := by
      intro he; have hv := congrArg Fin.val he; simp only [Fin.val_natAdd,Fin.val_castAdd,coreWidth] at hv; omega
    simp [nativePE,packState,initialState,nativeRawInput,readRow,cleanFlat,cleanCore,h]

theorem native_transformer_evaluation {n D : ℕ} (hn : 0 < n) (T : FiveBlockTransformer n D)
    (a s : ℝ) (x : Fin n → Fin D → ℝ) (y : Fin D → ℝ) :
    generalTransformer (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y)
      nativeSoftmax nativeActivation Fin.castSucc a s (Fin.last n) = T.eval a s x y := by
  unfold generalTransformer
  simp only [nativeLift,fixedTimeLift,nativeParameter]
  rw [read_row_action]
  change generalState (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y)
    nativeSoftmax nativeActivation Fin.castSucc a s 5 (Fin.last n) (valueFlat D) = _
  have hstep (k : ℕ) (hk : k<5) :
      generalState (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y)
        nativeSoftmax nativeActivation Fin.castSucc a s (k+1) =
      generalBlock (nativeLift T) ⟨k,hk⟩ (nativeSoftmax ⟨k,hk⟩) (nativeActivation ⟨k,hk⟩) Fin.castSucc a s
        (generalState (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y)
          nativeSoftmax nativeActivation Fin.castSucc a s k) := by
    rw [generalState,dite_eq_left hk]
  rw [hstep 4 (by decide),hstep 3 (by decide),hstep 2 (by decide),hstep 1 (by decide),hstep 0 (by decide)]
  have hb (j : ℕ) (hj : j<4) (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
      generalBlock (nativeLift T) ⟨j,lt_trans hj (by decide)⟩
        (nativeSoftmax ⟨j,lt_trans hj (by decide)⟩) (nativeActivation ⟨j,lt_trans hj (by decide)⟩)
        Fin.castSucc a s H = T.reluBlock ⟨j,hj⟩ a s H := by
    have he : (⟨j,hj⟩ : Fin 4).castSucc = (⟨j,lt_trans hj (by decide)⟩ : Fin 5) := Fin.ext rfl
    simpa only [he] using native_relu_block T ⟨j,hj⟩ a s H
  rw [hb 0 (by decide),hb 1 (by decide),hb 2 (by decide),hb 3 (by decide)]
  have hf (H : Fin (n+1) → Fin (embedWidth D) → ℝ) :
      generalBlock (nativeLift T) ⟨4,by decide⟩ (nativeSoftmax ⟨4,by decide⟩) (nativeActivation ⟨4,by decide⟩)
        Fin.castSucc a s H = T.finalBlock a s H := by
    have he : (4:Fin 5) = (⟨4,by decide⟩:Fin 5) := by apply Fin.ext; decide
    simpa only [he] using native_final_block hn T a s H
  rw [hf]
  change T.finalBlock a s (T.reluBlock 3 a s (T.reluBlock 2 a s (T.reluBlock 1 a s
    (T.reluBlock 0 a s (generalEmbedding (nativeLift T) (nativePE n D) (fun _ _ => 1) (nativeRawInput x y))))))
    (Fin.last n) (valueFlat D) = _
  rw [native_embedding]
  rfl

#print axioms cast_six_ffn_eval
#print axioms cast_six_ffn_bounded
#print axioms native_scheduled_matrix
#print axioms native_general_head
#print axioms native_affine_matrix
#print axioms native_affine_bias
#print axioms native_affine_step
#print axioms native_general_ffn
#print axioms zero_scheduled_head_masked
#print axioms native_relu_block
#print axioms native_final_block
#print axioms native_embedding
#print axioms native_transformer_evaluation
end GeneralizationCheck
