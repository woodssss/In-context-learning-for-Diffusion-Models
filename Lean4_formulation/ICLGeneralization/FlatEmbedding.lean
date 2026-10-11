module

public import ICLGeneralization.MatrixSelection
public import ICLGeneralization.FiveBlockRealization

@[expose] public section

open Matrix
namespace GeneralizationCheck

abbrev coreWidth (D : ℕ) := (D+1)+(D+2)
abbrev embedWidth (D : ℕ) := coreWidth D+3

def cleanCore {D : ℕ} (r : Fin D) : Fin (coreWidth D) := (r.castAdd 1).castAdd (D+2)
def valueCore (D : ℕ) : Fin (coreWidth D) := (Fin.last D).castAdd (D+2)
def differenceCore {D : ℕ} (r : Fin D) : Fin (coreWidth D) := Fin.natAdd (D+1) (r.castAdd 2)
def logitCore (D : ℕ) : Fin (coreWidth D) := Fin.natAdd (D+1) (Fin.natAdd D (0 : Fin 2))
def auxiliaryCore (D : ℕ) : Fin (coreWidth D) := Fin.natAdd (D+1) (Fin.natAdd D (1 : Fin 2))
def cleanFlat {D : ℕ} (r : Fin D) : Fin (embedWidth D) := (cleanCore r).castAdd 3
def valueFlat (D : ℕ) : Fin (embedWidth D) := (valueCore D).castAdd 3
def differenceFlat {D : ℕ} (r : Fin D) : Fin (embedWidth D) := (differenceCore r).castAdd 3
def logitFlat (D : ℕ) : Fin (embedWidth D) := (logitCore D).castAdd 3

noncomputable def packCore {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    Fin (coreWidth D) → ℝ :=
  Fin.addCases (Fin.addCases (H.data q) (fun _ : Fin 1 => H.value q))
    (Fin.addCases (H.difference q) (fun p : Fin 2 => ![H.logit q,0] p))

noncomputable def packState {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    Fin (embedWidth D) → ℝ :=
  Fin.addCases (packCore H q)
    (fun p : Fin 3 => ![Real.cos (tokenAngle (n+1) q),Real.sin (tokenAngle (n+1) q),1] p)

theorem pack_clean {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) (r : Fin D) :
    packState H q (cleanFlat r) = H.data q r := by
  simp [packState, packCore, cleanFlat, cleanCore]

theorem pack_value {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    packState H q (valueFlat D) = H.value q := by
  change packState H q ((Fin.natAdd D (0 : Fin 1)).castAdd (D+2) |>.castAdd 3) = _
  simp [packState, packCore]

theorem pack_difference {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) (r : Fin D) :
    packState H q (differenceFlat r) = H.difference q r := by
  simp [packState, packCore, differenceFlat, differenceCore]

theorem pack_logit {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    packState H q (logitFlat D) = H.logit q := by
  simp [packState, packCore, logitFlat, logitCore]

theorem pack_cosine {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    packState H q (cosineRow (coreWidth D)) = Real.cos (tokenAngle (n+1) q) := by
  change packState H q (Fin.natAdd (coreWidth D) (0 : Fin 3)) = _
  simp [packState]

theorem pack_sine {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    packState H q (sineRow (coreWidth D)) = Real.sin (tokenAngle (n+1) q) := by
  change packState H q (Fin.natAdd (coreWidth D) (1 : Fin 3)) = _
  simp [packState]

theorem pack_constant {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1)) :
    packState H q (constantRow (coreWidth D)) = 1 := by
  change packState H q (Fin.natAdd (coreWidth D) (2 : Fin 3)) = _
  simp [packState]

theorem flat_embedding_dimension (D : ℕ) : embedWidth D = 2*D+6 := by
  unfold embedWidth coreWidth
  omega

noncomputable def constantData (D : ℕ) : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ :=
  fun r c => if r=logitCore D then readRow (constantRow (coreWidth D)) c else 0

theorem constant_data_action {n D : ℕ} (H : RealizationState n D) (q : Fin (n+1))
    (r : Fin (coreWidth D)) :
    (constantData D).mulVec (packState H q) r = if r=logitCore D then 1 else 0 := by
  classical
  unfold constantData Matrix.mulVec dotProduct
  split_ifs with hr <;> simp [hr, read_row_action, pack_constant]

theorem constant_data_score {n D : ℕ} (H : RealizationState n D) (q k : Fin (n+1)) :
    (∑ r, (constantData D).mulVec (packState H q) r *
      (constantData D).mulVec (packState H k) r) = 1 := by
  classical
  simp [constant_data_action]

noncomputable def matrixReLUHead {d ℓ : ℕ} (Q K V : Matrix (Fin d) (Fin d) ℝ)
    (H : Fin ℓ → Fin d → ℝ) (q : Fin ℓ) (r : Fin d) : ℝ :=
  ∑ k, max 0 (∑ p, Q.mulVec (H q) p*K.mulVec (H k) p)*V.mulVec (H k) r

noncomputable def selectedMatrixHead (n D : ℕ) (B : ℝ) (target source : Fin (n+1))
    (Q K : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ)
    (V : Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ) :
    (Fin (n+1) → Fin (embedWidth D) → ℝ) → Fin (n+1) → Fin (embedWidth D) → ℝ :=
  matrixReLUHead
    (extendedQuery (coreWidth D) (n+1) (2*B*(n+1 : ℝ)^2) target Q)
    (extendedKey (coreWidth D) (n+1) (2*B*(n+1 : ℝ)^2) source K) V

theorem selected_matrix_head_state {n D : ℕ} (H : RealizationState n D) (B : ℝ)
    (target source : Fin (n+1))
    (Q K : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ)
    (V : Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ)
    (q : Fin (n+1)) (r : Fin (embedWidth D)) :
    selectedMatrixHead n D B target source Q K V (packState H) q r =
    reluHead (n+1) B target source
      (fun q k => ∑ p, Q.mulVec (packState H q) p*K.mulVec (packState H k) p)
      (fun k => V.mulVec (packState H k) r) q := by
  unfold selectedMatrixHead matrixReLUHead reluHead
  simp_rw [extended_matrix_score (coreWidth D) (n+1) _ target source _ _ Q K
    (packState H) (pack_cosine H) (pack_sine H) (pack_constant H)]
  simp only [Nat.cast_add, Nat.cast_one]

#print axioms pack_clean
#print axioms pack_value
#print axioms pack_difference
#print axioms pack_logit
#print axioms pack_cosine
#print axioms pack_sine
#print axioms pack_constant
#print axioms flat_embedding_dimension
#print axioms constant_data_action
#print axioms constant_data_score
#print axioms selected_matrix_head_state
end GeneralizationCheck
