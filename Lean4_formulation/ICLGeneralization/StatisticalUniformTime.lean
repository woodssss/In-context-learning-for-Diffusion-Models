module

public import ICLGeneralization.LemmaTwoGaussian
public import ICLGeneralization.LemmaThreeGaussian

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem lemma_two_uniform_time_original {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ<1)
    (n D w L F m K J N : ℕ) (hn : 0<n) (hD : 0<D) (hw : 0<w) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (S : Set (KernelSpace D)) (a s : (LegalTime δ) → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (hp : ∀ q r, |PE q r|≤1) (ht : ∀ q r, |tokenMask q r|≤1)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (layout : Fin D → FixedTimeLayout w L m) (κ R b s0 : ℝ)
    (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0≤κ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t ∧ s t≤1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (learn : HierarchicalTrainingSample Θ (CleanPromptSample n D S) (GaussianCoverSample (LegalTime δ) n D S) K J N →
      admissibleFixedTimeParameters (gaussianLossSetup n D w L F m (S:=S) a s (noiseRadius D s0)
        PE tokenMask softmax activation) layout κ R) (hl : Measurable learn) :
    let f := fun θ => fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s (noiseRadius D s0)
      PE tokenMask softmax activation layout θ.val
    let B := verifiedLossCoverConstant D w m (n+1) F L κ R b s0 (max 1 (b+noiseRadius D s0))
    let M := lossEnvelope D R b s0
    (∫ z, adaptiveHierarchyGap K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) f learn z
      ∂hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) ≤
    4*M*hierarchicalSamplingFactor K J N*
      (6*Real.sqrt ((D*fixedTimeParameterCount D w L F m:ℝ)*Real.log (B*Real.sqrt ((K*J)*N:ℝ)/M))+1)+
      M*(gaussianNoiseLaw D {eps | noiseRadius D s0<‖eps‖}).toReal := by
  let : Fact (δ<1) := ⟨hδ⟩
  exact lemma_two_gaussian_original n D w L F m K J N hn hD hw hK hJ hN S a s ham hsm
    PE tokenMask hp ht softmax activation layout κ R b s0 hLayout hκ hb hR hs0 ha hs hbox
    (uniformTimeLaw δ) μTask ρ learn hl

theorem lemma_three_uniform_time_original {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ<1)
    (n D w L F m K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (S : Set (KernelSpace D)) (a s : (LegalTime δ) → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (layout : Fin D → FixedTimeLayout w L m) (κ R b s0 C ε : ℝ)
    (hR : 0≤R) (hb : 0≤b) (hs0 : 0<s0) (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (θ : VectorFixedTimeParameter D w L F m → ℝ)
    (hθ : θ ∈ admissibleFixedTimeParameters
      (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout κ R)
    (hε : 0<ε) (hε1 : ε<1) :
    let f := fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s C PE tokenMask softmax activation layout θ
    let law := hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))
    (∫ z, hierarchicalEmpiricalLoss K J N f z-hierarchicalPopulationLoss μTask
      (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) f ∂law) ≤
      lossEnvelope D R b s0*Real.sqrt (Real.log (1/ε)/2)*hierarchicalSamplingFactor K J N+6*ε*lossEnvelope D R b s0 := by
  let : Fact (δ<1) := ⟨hδ⟩
  exact lemma_three_gaussian_original n D w L F m K J N hK hJ hN S a s ham hsm
    PE tokenMask softmax activation layout κ R b s0 C ε hR hb hs0 ha hs hbox
    (uniformTimeLaw δ) μTask ρ θ hθ hε hε1

#print axioms lemma_two_uniform_time_original
#print axioms lemma_three_uniform_time_original
end GeneralizationCheck
