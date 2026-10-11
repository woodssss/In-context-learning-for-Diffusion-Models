module

public import ICLGeneralization.FullGaussianLoss

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem lemma_three_gaussian_original {Time Θ : Type*} [MeasurableSpace Time] [MeasurableSpace Θ]
    (n D w L F m K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (S : Set (KernelSpace D)) (a s : Time → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (layout : Fin D → FixedTimeLayout w L m) (κ R b s0 C ε : ℝ)
    (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0) (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (θ : VectorFixedTimeParameter D w L F m → ℝ)
    (hθ : θ ∈ admissibleFixedTimeParameters
      (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout κ R)
    (hε : 0<ε) (hε1 : ε<1) :
    let f := fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s C PE tokenMask softmax activation layout θ
    let law := hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
    (∫ z, hierarchicalEmpiricalLoss K J N f z-hierarchicalPopulationLoss μTask
      (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime) f ∂law) ≤
      lossEnvelope D R b s0*Real.sqrt (Real.log (1/ε)/2)*hierarchicalSamplingFactor K J N+6*ε*lossEnvelope D R b s0 := by
  dsimp only
  let model := gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation
  have he : fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s C PE tokenMask softmax activation layout θ =
      fullFixedTimeLoss model layout θ := by
    funext p
    exact full_gaussian_loss_is_DSM n D w L F m a s C PE tokenMask softmax activation layout θ p
      (ne_of_gt (lt_of_lt_of_le hs0 (hs p.1)))
  rw [he]
  apply lemma_three_original_bound K J N hK hJ hN μTask (cleanPromptKernel n D ρ)
    (timeNoiseEpisodeKernel n D S μTime) _
    (full_fixed_loss_measurable model layout θ (measurable_gaussian_raw_input n D S a s ham hsm)
      (ham.comp measurable_fst) (hsm.comp measurable_fst)
      (fun j => (measurable_clean_coordinate j).comp measurable_snd.fst.fst))
    (lossEnvelope D R b s0) (by unfold lossEnvelope; positivity)
    (full_fixed_loss_envelope model layout θ κ R b s0 hθ hR hb hs0
      (fun p => ha p.1) (fun p => hs p.1) (fun p j => abs_le.mpr (hbox _ p.2.1.1.property j))) ε hε hε1

#print axioms lemma_three_gaussian_original
end GeneralizationCheck
