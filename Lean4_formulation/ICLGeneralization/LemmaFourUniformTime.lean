module

public import ICLGeneralization.LemmaFourGaussian

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped UniformConvergence NNReal ENNReal
namespace GeneralizationCheck

theorem lemma_four_uniform_time {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ < 1)
    (n D w L F m : ℕ) (hn : 0 < n) (S : Set (KernelSpace D))
    (a s : LegalTime δ → ℝ) (ha : Measurable a) (hs : Measurable s)
    (κ R b s0 η : ℝ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0)
    (haRange : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hsRange : ∀ t, s0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (hp : ∀ q r, |PE q r| ≤ 1) (ht : ∀ q r, |tokenMask q r| ≤ 1)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0) :
    let model := gaussianLossSetup n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation
    let A := admissibleGeneralParameters model κ R
    let f := generalGaussianDenoisingLoss n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation
    let B := verifiedLossCoverConstant D w m (n+1) F L κ R b s0 (max 1 (b+noiseRadius D s0))
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A f) (D*generalParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A (averagedFamily f (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))))
      (D*generalParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass A (averagedFamily (averagedFamily f (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) (cleanPromptKernel n D ρ)))
      (D*generalParameterCount D w L F m) B := by
  let : Fact (δ < 1) := ⟨hδ⟩
  exact lemma_four_gaussian_complete n D w L F m hn S a s ha hs κ R b s0 η
    hκ hR hb hs0 haRange hsRange hbox PE tokenMask hp ht softmax activation
    (uniformTimeLaw δ) ρ hη hηM

#print axioms lemma_four_uniform_time
end GeneralizationCheck
