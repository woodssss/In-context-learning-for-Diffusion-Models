module

public import ICLGeneralization.KernelCoverTransfer

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped UniformConvergence NNReal ENNReal
namespace GeneralizationCheck

noncomputable def paperParameterCount (D w L F m : ℕ) : ℕ :=
  w*(D+1)+L*(3*w^2*m+F*w^2)

noncomputable def verifiedLossCoverConstant (D w m ℓ F L : ℕ) (κ R b s0 U : ℝ) : ℝ :=
  entropyRadius κ (lossSensitivity D w m ℓ F L κ R b s0 U) (lossEnvelope D R b s0)

def FiniteEntropyBound {X : Type*} (η : ℝ≥0) (A : Set (X →ᵤ ℝ)) (P : ℕ) (B : ℝ) : Prop :=
  Metric.coveringNumber η A ≠ ⊤ ∧
    Real.log ((Metric.coveringNumber η A).toNat : ℝ) ≤ (P : ℝ)*Real.log (B/η.val)

theorem general_parameter_count_le_three_paper (D w L F m : ℕ) :
    generalParameterCount D w L F m ≤ 3*paperParameterCount D w L F m := by
  have hw : w ≤ w^2 := by
    by_cases h : w=0
    · simp [h]
    · have : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr h
      nlinarith
  have hff : F*(w^2+w) ≤ 3*(F*w^2) := by
    calc
      _ ≤ F*(w^2+w^2) := Nat.mul_le_mul_left F (Nat.add_le_add_left hw _)
      _ ≤ _ := by nlinarith
  have hh : 9*m*w^2+F*(w^2+w) ≤ 3*(3*w^2*m+F*w^2) := by nlinarith
  have he : w*D+w ≤ 3*(w*(D+1)) := by nlinarith
  calc
    generalParameterCount D w L F m = (w*D+w)+L*(9*m*w^2+F*(w^2+w)) := by unfold generalParameterCount; ring
    _ ≤ 3*(w*(D+1))+L*(3*(3*w^2*m+F*w^2)) := Nat.add_le_add he (Nat.mul_le_mul_left L hh)
    _ = _ := by unfold paperParameterCount; ring

theorem vector_general_parameter_count (D w L F m : ℕ) :
    Fintype.card (VectorGeneralParameter D w L F m) = D*generalParameterCount D w L F m := by
  simp only [VectorGeneralParameter,Fintype.card_prod,Fintype.card_fin,general_parameter_count]

theorem finite_entropy_bound_mono {X : Type*} (η : ℝ≥0) (A : Set (X →ᵤ ℝ)) (P Q : ℕ) (B : ℝ)
    (h : FiniteEntropyBound η A P B) (hPQ : P ≤ Q) (hB : 1 ≤ B/η.val) :
    FiniteEntropyBound η A Q B := by
  refine ⟨h.1,h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg hB)
  exact_mod_cast hPQ

/- Complete cover theorem for the full independently trainable scheduled
   matrix/affine family. The verified constant is a layer recurrence; the
   coefficient count includes all affine biases and schedule components. -/
theorem lemma_four_complete {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {D w L F m ℓ n : ℕ} (hn : 0 < n) (S : TransformerLossSetup Ω D w L F m ℓ n)
    (κ R b s0 U η : ℝ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0) (hU : 0 ≤ U)
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0)
    (hp : ∀ q r, |S.PE q r| ≤ 1) (ht : ∀ q r, |S.tokenMask q r| ≤ 1)
    (ha : ∀ ω, 0 ≤ S.alpha ω ∧ S.alpha ω ≤ 1) (hs : ∀ ω, s0 ≤ S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j| ≤ b) (hx : ∀ ω ∈ S.event, ∀ q r, |S.input ω q r| ≤ U)
    (hxm : ∀ q r, Measurable (fun ω => S.input ω q r)) (ham : Measurable S.alpha) (hsm : Measurable S.sigma)
    (hzm : ∀ j, Measurable (fun ω => S.clean ω j)) (hem : MeasurableSet S.event)
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (κTask : Kernel Y X) [IsMarkovKernel κTask] :
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R) (restrictedGeneralLoss S))
      (D*generalParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R) (averagedFamily (restrictedGeneralLoss S) κEpisode))
      (D*generalParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R)
        (averagedFamily (averagedFamily (restrictedGeneralLoss S) κEpisode) κTask))
      (D*generalParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) := by
  let A := admissibleGeneralParameters S κ R
  let f := restrictedGeneralLoss S
  let K := lossSensitivity D w m ℓ F L κ R b s0 U
  let M := lossEnvelope D R b s0
  have hK : 0 ≤ K := by
    have h := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
    unfold K lossSensitivity transformerSensitivity lossConversion
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg h.1 (mul_nonneg hκ h.2)))
  have hA : ∀ θ ∈ A, ∀ p, |θ p| ≤ κ := fun θ hθ => hθ.1
  have hf (θ) (_hθ : θ ∈ A) : Measurable (f θ) :=
    measurable_restricted_general_loss S θ hxm ham hsm hzm hem
  have hbnd : ∀ θ ∈ A, ∀ ω, |f θ ω| ≤ M := fun θ hθ =>
    restricted_general_loss_envelope S θ κ R b s0 hθ hR hb hs0 ha hs hz
  have hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ p, |θ p-θ' p| ≤ ε) →
      ∀ ω, |f θ ω-f θ' ω| ≤ K*ε := fun θ hθ θ' hθ' ε hε he =>
    restricted_general_loss_perturbation hn S θ θ' κ R b s0 U ε hκ hR hb hs0 hU hε
      hθ hθ' he hp ht ha hs hz hx
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
  simpa only [vector_general_parameter_count,A,f,K,M] using And.intro h (And.intro hh hg)

theorem lemma_four_paper_order {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {D w L F m ℓ n : ℕ} (hn : 0 < n) (S : TransformerLossSetup Ω D w L F m ℓ n)
    (κ R b s0 U η : ℝ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0) (hU : 0 ≤ U)
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0)
    (hp : ∀ q r, |S.PE q r| ≤ 1) (ht : ∀ q r, |S.tokenMask q r| ≤ 1)
    (ha : ∀ ω, 0 ≤ S.alpha ω ∧ S.alpha ω ≤ 1) (hs : ∀ ω, s0 ≤ S.sigma ω)
    (hz : ∀ ω j, |S.clean ω j| ≤ b) (hx : ∀ ω ∈ S.event, ∀ q r, |S.input ω q r| ≤ U)
    (hxm : ∀ q r, Measurable (fun ω => S.input ω q r)) (ham : Measurable S.alpha) (hsm : Measurable S.sigma)
    (hzm : ∀ j, Measurable (fun ω => S.clean ω j)) (hem : MeasurableSet S.event)
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode] (κTask : Kernel Y X) [IsMarkovKernel κTask] :
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R) (restrictedGeneralLoss S))
      (3*D*paperParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R) (averagedFamily (restrictedGeneralLoss S) κEpisode))
      (3*D*paperParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass (admissibleGeneralParameters S κ R)
        (averagedFamily (averagedFamily (restrictedGeneralLoss S) κEpisode) κTask))
      (3*D*paperParameterCount D w L F m) (verifiedLossCoverConstant D w m ℓ F L κ R b s0 U) := by
  obtain ⟨hf,hh,hg⟩ := lemma_four_complete hn S κ R b s0 U η hκ hR hb hs0 hU hη hηM
    hp ht ha hs hz hx hxm ham hsm hzm hem κEpisode κTask
  have hcount : D*generalParameterCount D w L F m ≤ 3*D*paperParameterCount D w L F m := by
    simpa only [mul_assoc,mul_left_comm] using Nat.mul_le_mul_left D (general_parameter_count_le_three_paper D w L F m)
  have hB : 1 ≤ verifiedLossCoverConstant D w m ℓ F L κ R b s0 U/η := by
    have hK : 0 ≤ lossSensitivity D w m ℓ F L κ R b s0 U := by
      have h := network_bounds_nonnegative D w m ℓ F κ s0 U hκ hs0 hU L
      unfold lossSensitivity transformerSensitivity lossConversion
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (add_nonneg h.1 (mul_nonneg hκ h.2)))
    apply (le_div_iff₀ hη).mpr
    unfold verifiedLossCoverConstant entropyRadius
    nlinarith
  exact ⟨finite_entropy_bound_mono _ _ _ _ _ hf hcount hB,
    finite_entropy_bound_mono _ _ _ _ _ hh hcount hB,finite_entropy_bound_mono _ _ _ _ _ hg hcount hB⟩

#print axioms general_parameter_count_le_three_paper
#print axioms vector_general_parameter_count
#print axioms finite_entropy_bound_mono
#print axioms lemma_four_complete
#print axioms lemma_four_paper_order
end GeneralizationCheck
