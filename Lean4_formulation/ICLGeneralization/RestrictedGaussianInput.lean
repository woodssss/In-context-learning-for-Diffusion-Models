module

public import ICLGeneralization.LemmaFourComplete
public import ICLGeneralization.PropositionOneUniformTime

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

abbrev GaussianCoverSample (Time : Type*) (n D : ℕ) (S : Set (KernelSpace D)) := Time × EpisodeSample n D S

noncomputable def gaussianRawInput {Time : Type*} (n D : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (p : GaussianCoverSample Time n D S) (q : Fin (n+1)) (j : Fin D) : ℝ :=
  if h : q.val < n then (p.2.2 ⟨q.val,h⟩).val j else a p.1*p.2.1.1.val j+s p.1*p.2.1.2 j

noncomputable def gaussianLossSetup {Time : Type*} (n D w L F m : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (C : ℝ) (PE tokenMask : Fin (n+1) → Fin w → ℝ)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool) :
    TransformerLossSetup (GaussianCoverSample Time n D S) D w L F m (n+1) n where
  PE := PE
  tokenMask := tokenMask
  input := gaussianRawInput n D a s
  softmax := softmax
  activation := activation
  mask := Fin.castSucc
  readToken := Fin.last n
  alpha p := a p.1
  sigma p := s p.1
  clean p j := p.2.1.1.val j
  event := {p | ‖p.2.1.2‖ ≤ C}

theorem gaussian_raw_input_bound {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (a s : Time → ℝ) (b C : ℝ) (_hb : 0 ≤ b) (hC : 0 ≤ C)
    (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hs : ∀ t, 0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (p : GaussianCoverSample Time n D S) (heps : ‖p.2.1.2‖ ≤ C) (q : Fin (n+1)) (j : Fin D) :
    |gaussianRawInput n D a s p q j| ≤ max 1 (b+C) := by
  unfold gaussianRawInput
  split_ifs with h
  · exact (abs_le.mpr (hbox _ (p.2.2 ⟨q.val,h⟩).property j)).trans
      ((le_add_of_nonneg_right hC).trans (le_max_right _ _))
  · have hz : |p.2.1.1.val j| ≤ b := abs_le.mpr (hbox _ p.2.1.1.property j)
    have he : |p.2.1.2 j| ≤ C := by
      exact (show |p.2.1.2 j| ≤ ‖p.2.1.2‖ from by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.2.1.2 j).trans heps
    have hza : |a p.1*p.2.1.1.val j| ≤ b := by
      rw [abs_mul,abs_of_nonneg (ha p.1).1]
      exact (mul_le_mul (ha p.1).2 hz (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have hes : |s p.1*p.2.1.2 j| ≤ C := by
      rw [abs_mul,abs_of_nonneg (hs p.1).1]
      exact (mul_le_mul (hs p.1).2 he (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    exact ((abs_add_le _ _).trans (add_le_add hza hes)).trans (le_max_right _ _)

theorem measurable_gaussian_raw_input {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (a s : Time → ℝ) (ha : Measurable a) (hs : Measurable s)
    (q : Fin (n+1)) (j : Fin D) : Measurable (fun p : GaussianCoverSample Time n D S => gaussianRawInput n D a s p q j) := by
  unfold gaussianRawInput
  split_ifs
  · exact (measurable_clean_coordinate j).comp ((measurable_pi_apply _).comp measurable_snd.snd)
  · exact ((ha.comp measurable_fst).mul ((measurable_clean_coordinate j).comp measurable_snd.fst.fst)).add
      ((hs.comp measurable_fst).mul ((PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) j).measurable.comp measurable_snd.fst.snd))

noncomputable def generalGaussianDenoisingLoss {Time : Type*} (n D w L F m : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (C : ℝ) (PE tokenMask : Fin (n+1) → Fin w → ℝ)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (θ : VectorGeneralParameter D w L F m → ℝ) (p : GaussianCoverSample Time n D S) : ℝ := by
  classical
  let mean := generalMean (gaussianLossSetup n D w L F m a s C PE tokenMask softmax activation) θ p
  let y := episodeQuery n D (a p.1) (s p.1) p.2
  exact if ‖p.2.1.2‖ ≤ C then ∑ j, (-y j/(s p.1)^2+a p.1/(s p.1)^2*mean j+p.2.1.2 j/s p.1)^2 else 0

theorem restricted_gaussian_loss_is_DSM {Time : Type*} (n D w L F m : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (C : ℝ) (PE tokenMask : Fin (n+1) → Fin w → ℝ)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (θ : VectorGeneralParameter D w L F m → ℝ) (p : GaussianCoverSample Time n D S) (hs : s p.1 ≠ 0) :
    generalGaussianDenoisingLoss n D w L F m a s C PE tokenMask softmax activation θ p =
      restrictedGeneralLoss (gaussianLossSetup n D w L F m a s C PE tokenMask softmax activation) θ p := by
  classical
  let G := generalMean (gaussianLossSetup n D w L F m a s C PE tokenMask softmax activation) θ p
  change (if ‖p.2.1.2‖ ≤ C then ∑ j,
      (-episodeQuery n D (a p.1) (s p.1) p.2 j/(s p.1)^2+a p.1/(s p.1)^2*G j+p.2.1.2 j/s p.1)^2 else 0) =
    (if ‖p.2.1.2‖ ≤ C then (a p.1)^2/(s p.1)^4*∑ j, (G j-p.2.1.1.val j)^2 else 0)
  split_ifs
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hh := residual_cancel (a p.1) (s p.1) (G j) (p.2.1.1.val j) (p.2.1.2 j) hs
    change (-(a p.1*p.2.1.1.val j+s p.1*p.2.1.2 j)/(s p.1)^2+
      a p.1/(s p.1)^2*G j+p.2.1.2 j/s p.1)^2 = _
    convert congrArg (fun v : ℝ => v^2) hh using 1
    all_goals ring
  · rfl

#print axioms gaussian_raw_input_bound
#print axioms measurable_gaussian_raw_input
#print axioms restricted_gaussian_loss_is_DSM
end GeneralizationCheck
