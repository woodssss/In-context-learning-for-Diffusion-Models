module

public import ICLGeneralization.GeneralNetworkStability
public import ICLGeneralization.Core

@[expose] public section
namespace GeneralizationCheck

structure TransformerLossSetup (Ω : Type*) (D w L F m ℓ n : ℕ) where
  PE : Fin ℓ → Fin w → ℝ
  tokenMask : Fin ℓ → Fin w → ℝ
  input : Ω → Fin ℓ → Fin D → ℝ
  softmax : Fin L → Bool
  activation : Fin L → Fin F → Bool
  mask : Fin n → Fin ℓ
  readToken : Fin ℓ
  alpha : Ω → ℝ
  sigma : Ω → ℝ
  clean : Ω → Fin D → ℝ
  event : Set Ω

abbrev VectorGeneralParameter (D w L F m : ℕ) := Fin D × GeneralParameter D w L F m

noncomputable def generalMean {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (θ : VectorGeneralParameter D w L F m → ℝ)
    (ω : Ω) (j : Fin D) : ℝ :=
  generalTransformer (fun p => θ (j,p)) S.PE S.tokenMask (S.input ω) S.softmax S.activation
    S.mask (S.alpha ω) (S.sigma ω) S.readToken

noncomputable def meanSquaredLoss (D : ℕ) (a s : ℝ) (g z : Fin D → ℝ) : ℝ :=
  a^2/s^4*∑ j, (g j-z j)^2

noncomputable def restrictedGeneralLoss {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (θ : VectorGeneralParameter D w L F m → ℝ)
    (ω : Ω) : ℝ := by
  classical
  exact if ω ∈ S.event then meanSquaredLoss D (S.alpha ω) (S.sigma ω)
      (generalMean S θ ω) (S.clean ω) else 0

noncomputable def admissibleGeneralParameters {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (κ R : ℝ) : Set (VectorGeneralParameter D w L F m → ℝ) :=
  {θ | (∀ p, |θ p| ≤ κ) ∧ ∀ ω j, |generalMean S θ ω j| ≤ R}

noncomputable def lossEnvelope (D : ℕ) (R b s0 : ℝ) : ℝ := (D : ℝ)*(R+b)^2/s0^4
noncomputable def lossConversion (D : ℕ) (R b s0 : ℝ) : ℝ := 2*(D : ℝ)*(R+b)/s0^4
noncomputable def lossSensitivity (D w m ℓ F L : ℕ) (κ R b s0 U : ℝ) : ℝ :=
  lossConversion D R b s0*transformerSensitivity D w m ℓ F L κ s0 U

theorem squared_loss_conversion (D : ℕ) (g h z : Fin D → ℝ) (R b E : ℝ)
    (_hR : 0 ≤ R) (_hb : 0 ≤ b) (hE : 0 ≤ E)
    (hg : ∀ j, |g j| ≤ R) (hh : ∀ j, |h j| ≤ R) (hz : ∀ j, |z j| ≤ b)
    (hd : ∀ j, |g j-h j| ≤ E) :
    |(∑ j, (g j-z j)^2)-(∑ j, (h j-z j)^2)| ≤ 2*(D : ℝ)*(R+b)*E := by
  rw [← Finset.sum_sub_distrib]
  have hp (j : Fin D) : |g j+h j-2*z j| ≤ 2*(R+b) := by
    have ha := (abs_add_le (g j) (h j)).trans (add_le_add (hg j) (hh j))
    have hz' : |2*z j| ≤ 2*b := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]; exact mul_le_mul_of_nonneg_left (hz j) (by norm_num)
    exact ((abs_sub _ _).trans (add_le_add ha hz')).trans_eq (by ring)
  have hx (j : Fin D) : |(g j-z j)^2-(h j-z j)^2| ≤ E*(2*(R+b)) := by
    have he : (g j-z j)^2-(h j-z j)^2 = (g j-h j)*(g j+h j-2*z j) := by ring
    rw [he,abs_mul]
    exact mul_le_mul (hd j) (hp j) (abs_nonneg _) hE
  exact (finite_sum_abs_bound D _ _ hx).trans_eq (by ring)

theorem schedule_square_bound (a s s0 : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s) :
    0 ≤ a^2/s^4 ∧ a^2/s^4 ≤ 1/s0^4 := by
  have hsp : 0 < s := lt_of_lt_of_le hs0 hs
  have ha2 : a^2 ≤ 1 := by nlinarith [ha.1,ha.2]
  exact ⟨by positivity,(div_le_div_of_nonneg_right ha2 (by positivity)).trans
    (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hs0.le hs 4))⟩

theorem mean_loss_conversion (D : ℕ) (a s s0 : ℝ) (g h z : Fin D → ℝ) (R b E : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hg : ∀ j, |g j| ≤ R) (hh : ∀ j, |h j| ≤ R) (hz : ∀ j, |z j| ≤ b)
    (hd : ∀ j, |g j-h j| ≤ E) :
    |meanSquaredLoss D a s g z-meanSquaredLoss D a s h z| ≤ lossConversion D R b s0*E := by
  unfold meanSquaredLoss
  rw [← mul_sub,abs_mul,abs_of_nonneg (schedule_square_bound a s s0 ha hs0 hs).1]
  exact (mul_le_mul (schedule_square_bound a s s0 ha hs0 hs).2
    (squared_loss_conversion D g h z R b E hR hb hE hg hh hz hd) (abs_nonneg _) (by positivity)).trans_eq
    (by unfold lossConversion; ring)

theorem mean_loss_envelope (D : ℕ) (a s s0 : ℝ) (g z : Fin D → ℝ) (R b : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s) (_hR : 0 ≤ R) (_hb : 0 ≤ b)
    (hg : ∀ j, |g j| ≤ R) (hz : ∀ j, |z j| ≤ b) :
    |meanSquaredLoss D a s g z| ≤ lossEnvelope D R b s0 := by
  have hv := vector_error_bound D g z R b (fun j => abs_le.mp (hg j)) (fun j => abs_le.mp (hz j))
  have hv0 : 0 ≤ ∑ j, (g j-z j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold meanSquaredLoss
  rw [abs_mul,abs_of_nonneg (schedule_square_bound a s s0 ha hs0 hs).1,abs_of_nonneg hv0]
  exact (mul_le_mul (schedule_square_bound a s s0 ha hs0 hs).2 hv hv0 (by positivity)).trans_eq
    (by unfold lossEnvelope; ring)

theorem restricted_general_loss_envelope {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (θ : VectorGeneralParameter D w L F m → ℝ)
    (κ R b s0 : ℝ) (hθ : θ ∈ admissibleGeneralParameters S κ R) (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hs0 : 0 < s0) (ha : ∀ ω, 0 ≤ S.alpha ω ∧ S.alpha ω ≤ 1) (hs : ∀ ω, s0 ≤ S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j| ≤ b) (ω : Ω) :
    |restrictedGeneralLoss S θ ω| ≤ lossEnvelope D R b s0 := by
  unfold restrictedGeneralLoss
  split_ifs
  · exact mean_loss_envelope D _ _ s0 _ _ R b (ha ω) hs0 (hs ω) hR hb (hθ.2 ω) (hz ω)
  · simp only [abs_zero]; unfold lossEnvelope; positivity

theorem restricted_general_loss_perturbation {Ω : Type*} {D w L F m ℓ n : ℕ}
    (hn : 0 < n) (S : TransformerLossSetup Ω D w L F m ℓ n)
    (θ θ' : VectorGeneralParameter D w L F m → ℝ) (κ R b s0 U ε : ℝ)
    (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0) (hU : 0 ≤ U) (hε : 0 ≤ ε)
    (hθ : θ ∈ admissibleGeneralParameters S κ R) (hθ' : θ' ∈ admissibleGeneralParameters S κ R)
    (he : ∀ p, |θ p-θ' p| ≤ ε) (hp : ∀ q r, |S.PE q r| ≤ 1) (ht : ∀ q r, |S.tokenMask q r| ≤ 1)
    (ha : ∀ ω, 0 ≤ S.alpha ω ∧ S.alpha ω ≤ 1) (hs : ∀ ω, s0 ≤ S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j| ≤ b) (hx : ∀ ω ∈ S.event, ∀ q r, |S.input ω q r| ≤ U) (ω : Ω) :
    |restrictedGeneralLoss S θ ω-restrictedGeneralLoss S θ' ω| ≤ lossSensitivity D w m ℓ F L κ R b s0 U*ε := by
  have hc : 0 ≤ transformerSensitivity D w m ℓ F L κ s0 U := by
    have hh := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
    exact mul_nonneg (by positivity) (add_nonneg hh.1 (mul_nonneg hκ hh.2))
  have hc' : 0 ≤ lossConversion D R b s0 := by unfold lossConversion; positivity
  unfold restrictedGeneralLoss
  split_ifs with h
  · have hmean (j : Fin D) : |generalMean S θ ω j-generalMean S θ' ω j| ≤
        transformerSensitivity D w m ℓ F L κ s0 U*ε :=
      general_transformer_perturbation hn (fun p => θ (j,p)) (fun p => θ' (j,p)) S.PE S.tokenMask
        (S.input ω) S.softmax S.activation S.mask (S.alpha ω) (S.sigma ω) κ s0 U ε
        hκ hs0 hU hε (ha ω) (hs ω) (fun p => hθ.1 _) (fun p => hθ'.1 _) (fun p => he _)
        hp ht (hx ω h) S.readToken
    exact (mean_loss_conversion D _ _ s0 _ _ _ R b _ (ha ω) hs0 (hs ω) hR hb (mul_nonneg hc hε)
      (hθ.2 ω) (hθ'.2 ω) (hz ω) hmean).trans_eq (by unfold lossSensitivity; ring)
  · simp only [sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg hc' hc) hε

#print axioms squared_loss_conversion
#print axioms schedule_square_bound
#print axioms mean_loss_conversion
#print axioms mean_loss_envelope
#print axioms restricted_general_loss_envelope
#print axioms restricted_general_loss_perturbation
end GeneralizationCheck
