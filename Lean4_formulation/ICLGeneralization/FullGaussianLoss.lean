module

public import ICLGeneralization.LemmaThreeComplete

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def fullFixedTimeLoss {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (ω : Ω) : ℝ :=
  meanSquaredLoss D (S.alpha ω) (S.sigma ω) (generalMean S (vectorFixedTimeLift layout θ) ω) (S.clean ω)

theorem full_fixed_loss_measurable {Ω : Type*} [MeasurableSpace Ω] {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ)
    (hx : ∀ q r, Measurable (fun ω => S.input ω q r)) (ha : Measurable S.alpha) (hs : Measurable S.sigma)
    (hz : ∀ j, Measurable (fun ω => S.clean ω j)) : Measurable (fullFixedTimeLoss S layout θ) := by
  have hg (j : Fin D) : Measurable (fun ω => generalMean S (vectorFixedTimeLift layout θ) ω j) :=
    measurable_general_transformer (fun p => vectorFixedTimeLift layout θ (j,p)) S.PE S.tokenMask S.input hx
      S.softmax S.activation S.mask S.alpha S.sigma ha hs S.readToken
  exact ((ha.pow_const 2).div (hs.pow_const 4)).mul
    (Finset.measurable_sum _ (fun j _ => ((hg j).sub (hz j)).pow_const 2))

theorem full_fixed_loss_envelope {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (κ R b s0 : ℝ)
    (hθ : θ ∈ admissibleFixedTimeParameters S layout κ R) (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0)
    (ha : ∀ ω, 0≤S.alpha ω ∧ S.alpha ω≤1) (hs : ∀ ω, s0≤S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j|≤b) (ω : Ω) : |fullFixedTimeLoss S layout θ ω|≤lossEnvelope D R b s0 :=
  mean_loss_envelope D _ _ s0 _ _ R b (ha ω) hs0 (hs ω) hR hb (hθ.2 ω) (hz ω)

noncomputable def fullFixedGaussianDenoisingLoss {Time : Type*} (n D w L F m : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (C : ℝ) (PE tokenMask : Fin (n+1) → Fin w → ℝ)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (p : GaussianCoverSample Time n D S) : ℝ :=
  let model := gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation
  let G := generalMean model (vectorFixedTimeLift layout θ) p
  let y := episodeQuery n D (a p.1) (s p.1) p.2
  ∑ j, (-y j/(s p.1)^2+a p.1/(s p.1)^2*G j+p.2.1.2 j/s p.1)^2

theorem full_gaussian_loss_is_DSM {Time : Type*} (n D w L F m : ℕ) {S : Set (KernelSpace D)}
    (a s : Time → ℝ) (C : ℝ) (PE tokenMask : Fin (n+1) → Fin w → ℝ)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (p : GaussianCoverSample Time n D S) (hs : s p.1≠0) :
    fullFixedGaussianDenoisingLoss n D w L F m a s C PE tokenMask softmax activation layout θ p =
      fullFixedTimeLoss (gaussianLossSetup n D w L F m a s C PE tokenMask softmax activation) layout θ p := by
  let G := generalMean (gaussianLossSetup n D w L F m a s C PE tokenMask softmax activation) (vectorFixedTimeLift layout θ) p
  change (∑ j, (-episodeQuery n D (a p.1) (s p.1) p.2 j/(s p.1)^2+
      a p.1/(s p.1)^2*G j+p.2.1.2 j/s p.1)^2) = (a p.1)^2/(s p.1)^4*∑ j, (G j-p.2.1.1.val j)^2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hh := residual_cancel (a p.1) (s p.1) (G j) (p.2.1.1.val j) (p.2.1.2 j) hs
  change (-(a p.1*p.2.1.1.val j+s p.1*p.2.1.2 j)/(s p.1)^2+
      a p.1/(s p.1)^2*G j+p.2.1.2 j/s p.1)^2 = _
  convert congrArg (fun v : ℝ => v^2) hh using 1
  all_goals ring

#print axioms full_fixed_loss_measurable
#print axioms full_fixed_loss_envelope
#print axioms full_gaussian_loss_is_DSM
end GeneralizationCheck
