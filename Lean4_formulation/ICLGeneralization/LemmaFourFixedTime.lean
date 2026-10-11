module

public import ICLGeneralization.FixedTimeParameterization

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped UniformConvergence NNReal ENNReal
namespace GeneralizationCheck

noncomputable def restrictedFixedTimeLoss {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) : Ω → ℝ :=
  restrictedGeneralLoss S (vectorFixedTimeLift layout θ)

noncomputable def admissibleFixedTimeParameters {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (κ R : ℝ) : Set (VectorFixedTimeParameter D w L F m → ℝ) :=
  {θ | (∀ p, |θ p| ≤ κ) ∧ ∀ ω j, |generalMean S (vectorFixedTimeLift layout θ) ω j| ≤ R}

theorem fixed_time_admissible_lift {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (κ R : ℝ) (hLayout : ∀ j, (layout j).Bounded κ)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (hθ : θ ∈ admissibleFixedTimeParameters S layout κ R) :
    vectorFixedTimeLift layout θ ∈ admissibleGeneralParameters S κ R :=
  ⟨fun p => fixed_time_lift_bounded (layout p.1) _ κ (hLayout p.1) (fun q => hθ.1 (p.1,q)) p.2,hθ.2⟩

theorem lemma_four_fixed_time {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {D w L F m ℓ n : ℕ} (hn : 0 < n) (S : TransformerLossSetup Ω D w L F m ℓ n)
    (layout : Fin D → FixedTimeLayout w L m)
    (κ R b s0 U η : ℝ) (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0) (hU : 0 ≤ U)
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0)
    (hp : ∀ q r, |S.PE q r| ≤ 1) (ht : ∀ q r, |S.tokenMask q r| ≤ 1)
    (ha : ∀ ω, 0 ≤ S.alpha ω ∧ S.alpha ω ≤ 1) (hs : ∀ ω, s0 ≤ S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j| ≤ b) (hx : ∀ ω ∈ S.event, ∀ q r, |S.input ω q r| ≤ U)
    (hxm : ∀ q r, Measurable (fun ω => S.input ω q r)) (ham : Measurable S.alpha) (hsm : Measurable S.sigma)
    (hzm : ∀ j, Measurable (fun ω => S.clean ω j)) (hem : MeasurableSet S.event)
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (κTask : Kernel Y X) [IsMarkovKernel κTask] :
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleFixedTimeParameters S layout κ R) (restrictedFixedTimeLoss S layout))
      (D*fixedTimeParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleFixedTimeParameters S layout κ R) (averagedFamily (restrictedFixedTimeLoss S layout) κEpisode))
      (D*fixedTimeParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleFixedTimeParameters S layout κ R)
        (averagedFamily (averagedFamily (restrictedFixedTimeLoss S layout) κEpisode) κTask))
      (D*fixedTimeParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) := by
  let A := admissibleFixedTimeParameters S layout κ R
  let f := restrictedFixedTimeLoss S layout
  let K := lossSensitivity D w m ℓ F L κ R b s0 U
  let M := lossEnvelope D R b s0
  have hK : 0 ≤ K := by
    have h := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
    unfold K lossSensitivity transformerSensitivity lossConversion
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg h.1 (mul_nonneg hκ h.2)))
  have hA : ∀ θ ∈ A, ∀ p, |θ p| ≤ κ := fun θ hθ => hθ.1
  have hf (θ) (_hθ : θ ∈ A) : Measurable (f θ) :=
    measurable_restricted_general_loss S (vectorFixedTimeLift layout θ) hxm ham hsm hzm hem
  have hbnd : ∀ θ ∈ A, ∀ ω, |f θ ω| ≤ M := fun θ hθ =>
    restricted_general_loss_envelope S (vectorFixedTimeLift layout θ) κ R b s0 (fixed_time_admissible_lift S layout κ R hLayout θ hθ) hR hb hs0 ha hs hz
  have hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ p, |θ p-θ' p| ≤ ε) →
      ∀ ω, |f θ ω-f θ' ω| ≤ K*ε := fun θ hθ θ' hθ' ε hε he =>
    restricted_general_loss_perturbation hn S (vectorFixedTimeLift layout θ) (vectorFixedTimeLift layout θ') κ R b s0 U ε hκ hR hb hs0 hU hε
      (fixed_time_admissible_lift S layout κ R hLayout θ hθ) (fixed_time_admissible_lift S layout κ R hLayout θ' hθ')
      (fun p => fixed_time_lift_perturbation (layout p.1) _ _ ε hε (fun q => he (p.1,q)) p.2) hp ht ha hs hz hx
  have h := parameterized_uniform_entropy A f κ K M η hκ hK hη hηM hA hLip
  have hhf (θ) (hθ : θ ∈ A) : Measurable (averagedFamily f κEpisode θ) :=
    kernel_average_measurable f κEpisode θ (hf θ hθ)
  have hhB : ∀ θ ∈ A, ∀ x, |averagedFamily f κEpisode θ x| ≤ M :=
    fun θ hθ => kernel_average_bounded f κEpisode θ (hf θ hθ) M (hbnd θ hθ)
  have hhLip := kernel_average_parameter_stability A f κEpisode K M hf hbnd hLip
  have hh := parameterized_uniform_entropy A (averagedFamily f κEpisode) κ K M η hκ hK hη hηM hA hhLip
  have hgLip := kernel_average_parameter_stability A (averagedFamily f κEpisode) κTask K M hhf hhB hhLip
  have hg := parameterized_uniform_entropy A (averagedFamily (averagedFamily f κEpisode) κTask)
    κ K M η hκ hK hη hηM hA hgLip
  unfold FiniteEntropyBound verifiedLossCoverConstant
  simpa only [vector_fixed_time_parameter_count,A,f,K,M] using And.intro h (And.intro hh hg)

#print axioms fixed_time_admissible_lift
#print axioms lemma_four_fixed_time
end GeneralizationCheck
