module

public import ICLGeneralization.LemmaFourFixedTime

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped UniformConvergence NNReal ENNReal
namespace GeneralizationCheck

theorem lemma_four_fixed_gaussian {Time Θ : Type*} [MeasurableSpace Time] [MeasurableSpace Θ]
    (n D w L F m : ℕ) (hn : 0 < n) (S : Set (KernelSpace D))
    (a s : Time → ℝ) (ha : Measurable a) (hs : Measurable s)
    (layout : Fin D → FixedTimeLayout w L m)
    (κ R b s0 η : ℝ) (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0)
    (haRange : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hsRange : ∀ t, s0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (hp : ∀ q r, |PE q r| ≤ 1) (ht : ∀ q r, |tokenMask q r| ≤ 1)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (μTime : Measure Time) [IsProbabilityMeasure μTime] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0) :
    let model := gaussianLossSetup n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation
    let A := admissibleFixedTimeParameters model layout κ R
    let f := fun θ => generalGaussianDenoisingLoss n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation (vectorFixedTimeLift layout θ)
    let B := verifiedLossCoverConstant D w m (n+1) F L κ R b s0 (max 1 (b+noiseRadius D s0))
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A f) (D*fixedTimeParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A (averagedFamily f (timeNoiseEpisodeKernel n D S μTime)))
      (D*fixedTimeParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass A (averagedFamily (averagedFamily f (timeNoiseEpisodeKernel n D S μTime)) (cleanPromptKernel n D ρ)))
      (D*fixedTimeParameterCount D w L F m) B := by
  dsimp only
  let model := gaussianLossSetup n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation
  have hsPos (t : Time) : 0 < s t := lt_of_lt_of_le hs0 (hsRange t).1
  have heq : (fun θ => generalGaussianDenoisingLoss n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation (vectorFixedTimeLift layout θ)) =
      restrictedFixedTimeLoss model layout := by
    funext θ p
    exact restricted_gaussian_loss_is_DSM n D w L F m a s (noiseRadius D s0) PE tokenMask softmax activation (vectorFixedTimeLift layout θ) p (ne_of_gt (hsPos p.1))
  rw [heq]
  apply lemma_four_fixed_time hn model layout κ R b s0 (max 1 (b+noiseRadius D s0)) η hLayout hκ hR hb hs0
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) hη hηM hp ht
    (fun p => haRange p.1) (fun p => (hsRange p.1).1)
    (fun p j => abs_le.mpr (hbox _ p.2.1.1.property j))
    (fun p h => gaussian_raw_input_bound n D S a s b (noiseRadius D s0) hb (noise_radius_nonnegative D s0)
      haRange (fun t => ⟨(hsPos t).le,(hsRange t).2⟩) hbox p h)
    (measurable_gaussian_raw_input n D S a s ha hs) (ha.comp measurable_fst) (hs.comp measurable_fst)
    (fun j => (measurable_clean_coordinate j).comp measurable_snd.fst.fst)
    (measurableSet_le (by fun_prop) measurable_const)
    (timeNoiseEpisodeKernel n D S μTime) (cleanPromptKernel n D ρ)

theorem lemma_four_fixed_uniform_time {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ < 1)
    (n D w L F m : ℕ) (hn : 0 < n) (S : Set (KernelSpace D))
    (a s : LegalTime δ → ℝ) (ha : Measurable a) (hs : Measurable s)
    (layout : Fin D → FixedTimeLayout w L m)
    (κ R b s0 η : ℝ) (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hb : 0 ≤ b) (hs0 : 0 < s0)
    (haRange : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hsRange : ∀ t, s0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (hp : ∀ q r, |PE q r| ≤ 1) (ht : ∀ q r, |tokenMask q r| ≤ 1)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (hη : 0 < η) (hηM : η ≤ lossEnvelope D R b s0) :
    let model := gaussianLossSetup n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation
    let A := admissibleFixedTimeParameters model layout κ R
    let f := fun θ => generalGaussianDenoisingLoss n D w L F m (S := S) a s (noiseRadius D s0) PE tokenMask softmax activation (vectorFixedTimeLift layout θ)
    let B := verifiedLossCoverConstant D w m (n+1) F L κ R b s0 (max 1 (b+noiseRadius D s0))
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A f) (D*fixedTimeParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩ (uniformFunctionClass A (averagedFamily f (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))))
      (D*fixedTimeParameterCount D w L F m) B ∧
    FiniteEntropyBound ⟨η,hη.le⟩
      (uniformFunctionClass A (averagedFamily (averagedFamily f (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) (cleanPromptKernel n D ρ)))
      (D*fixedTimeParameterCount D w L F m) B := by
  let : Fact (δ < 1) := ⟨hδ⟩
  exact lemma_four_fixed_gaussian n D w L F m hn S a s ha hs layout κ R b s0 η
    hLayout hκ hR hb hs0 haRange hsRange hbox PE tokenMask hp ht softmax activation
    (uniformTimeLaw δ) ρ hη hηM

#print axioms lemma_four_fixed_gaussian
#print axioms lemma_four_fixed_uniform_time
end GeneralizationCheck
