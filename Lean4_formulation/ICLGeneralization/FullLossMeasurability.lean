module

public import ICLGeneralization.FullGaussianLoss
public import ICLGeneralization.ParameterizedMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

noncomputable def pointInputRadius {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (ω : Ω) : ℝ := 1+∑ q, ∑ r, |S.input ω q r|

theorem point_input_radius_nonnegative {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (ω : Ω) : 0≤pointInputRadius S ω := by
  unfold pointInputRadius
  positivity

theorem point_input_radius_bound {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (ω : Ω) (q : Fin ℓ) (r : Fin D) :
    |S.input ω q r|≤pointInputRadius S ω := by
  have h1 := Finset.single_le_sum (f:=fun r => |S.input ω q r|) (fun i _ => abs_nonneg _) (Finset.mem_univ r)
  have h2 := Finset.single_le_sum (f:=fun q => ∑ r, |S.input ω q r|)
    (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ q)
  exact (h1.trans h2).trans (by unfold pointInputRadius; linarith)

theorem loss_sensitivity_nonnegative (D w m ℓ F L : ℕ) (κ R b s0 U : ℝ)
    (hκ : 0≤κ) (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0) (hU : 0≤U) :
    0≤lossSensitivity D w m ℓ F L κ R b s0 U := by
  have h := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
  unfold lossSensitivity transformerSensitivity lossConversion
  exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg h.1 (mul_nonneg hκ h.2)))

theorem full_fixed_loss_perturbation {Ω : Type*} {D w L F m ℓ n : ℕ}
    (hn : 0<n) (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ θ' : VectorFixedTimeParameter D w L F m → ℝ) (κ R b s0 U ε : ℝ)
    (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0≤κ) (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0)
    (hU : 0≤U) (hε : 0≤ε) (hθ : θ ∈ admissibleFixedTimeParameters S layout κ R)
    (hθ' : θ' ∈ admissibleFixedTimeParameters S layout κ R) (he : ∀ p, |θ p-θ' p|≤ε)
    (hp : ∀ q r, |S.PE q r|≤1) (ht : ∀ q r, |S.tokenMask q r|≤1)
    (ha : ∀ ω, 0≤S.alpha ω ∧ S.alpha ω≤1) (hs : ∀ ω, s0≤S.sigma ω) (hz : ∀ ω j, |S.clean ω j|≤b)
    (ω : Ω) (hx : ∀ q r, |S.input ω q r|≤U) :
    |fullFixedTimeLoss S layout θ ω-fullFixedTimeLoss S layout θ' ω|≤lossSensitivity D w m ℓ F L κ R b s0 U*ε := by
  have hc := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
  have hK : 0≤transformerSensitivity D w m ℓ F L κ s0 U := by
    unfold transformerSensitivity
    exact mul_nonneg (by positivity) (add_nonneg hc.1 (mul_nonneg hκ hc.2))
  have hθb := fixed_time_admissible_lift S layout κ R hLayout θ hθ
  have hθb' := fixed_time_admissible_lift S layout κ R hLayout θ' hθ'
  have hmean (j : Fin D) : |generalMean S (vectorFixedTimeLift layout θ) ω j-
      generalMean S (vectorFixedTimeLift layout θ') ω j|≤transformerSensitivity D w m ℓ F L κ s0 U*ε :=
    general_transformer_perturbation hn (fun p => vectorFixedTimeLift layout θ (j,p))
      (fun p => vectorFixedTimeLift layout θ' (j,p)) S.PE S.tokenMask (S.input ω) S.softmax S.activation S.mask
      (S.alpha ω) (S.sigma ω) κ s0 U ε hκ hs0 hU hε (ha ω) (hs ω)
      (fun p => hθb.1 (j,p)) (fun p => hθb'.1 (j,p))
      (fun p => fixed_time_lift_perturbation (layout j) _ _ ε hε (fun q => he (j,q)) p)
      hp ht hx S.readToken
  exact (mean_loss_conversion D _ _ s0 _ _ _ R b _ (ha ω) hs0 (hs ω) hR hb (mul_nonneg hK hε)
    (hθ.2 ω) (hθ'.2 ω) (hz ω) hmean).trans_eq (by unfold lossSensitivity; ring)

theorem full_fixed_loss_joint_measurable {Ω : Type*} [MeasurableSpace Ω] {D w L F m ℓ n : ℕ}
    (hn : 0<n) (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (κ R b s0 : ℝ) (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0≤κ) (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0)
    (hp : ∀ q r, |S.PE q r|≤1) (ht : ∀ q r, |S.tokenMask q r|≤1)
    (ha : ∀ ω, 0≤S.alpha ω ∧ S.alpha ω≤1) (hs : ∀ ω, s0≤S.sigma ω) (hz : ∀ ω j, |S.clean ω j|≤b)
    (hxm : ∀ q r, Measurable (fun ω => S.input ω q r)) (ham : Measurable S.alpha) (hsm : Measurable S.sigma)
    (hzm : ∀ j, Measurable (fun ω => S.clean ω j)) :
    Measurable (fun p : (admissibleFixedTimeParameters S layout κ R) × Ω => fullFixedTimeLoss S layout p.1.val p.2) := by
  let C := fun ω => lossSensitivity D w m ℓ F L κ R b s0 (pointInputRadius S ω)
  apply parameterized_loss_joint_measurable _ _ C
    (fun ω => loss_sensitivity_nonnegative D w m ℓ F L κ R b s0 _ hκ hR hb hs0 (point_input_radius_nonnegative S ω))
    (fun θ _ => full_fixed_loss_measurable S layout θ hxm ham hsm hzm)
  intro θ hθ θ' hθ' ε hε he ω
  exact full_fixed_loss_perturbation hn S layout θ θ' κ R b s0 (pointInputRadius S ω) ε hLayout hκ hR hb hs0
    (point_input_radius_nonnegative S ω) hε hθ hθ' he hp ht ha hs hz ω (point_input_radius_bound S ω)

#print axioms point_input_radius_nonnegative
#print axioms point_input_radius_bound
#print axioms loss_sensitivity_nonnegative
#print axioms full_fixed_loss_perturbation
#print axioms full_fixed_loss_joint_measurable
end GeneralizationCheck
