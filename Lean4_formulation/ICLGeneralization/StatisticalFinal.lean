module

public import ICLGeneralization.StatisticalRateAlgebra
public import ICLGeneralization.TrainingCorrespondence

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem lemma_two_uniform_time_rate {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ<1)
    (n D K J N : ℕ) (hn : 2≤n) (hD : 1≤D) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (S : Set (KernelSpace D)) (a s : (LegalTime δ) → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (PE tokenMask : Fin (n+1) → Fin (2*D+6) → ℝ) (hp : ∀ q r, |PE q r|≤1) (ht : ∀ q r, |tokenMask q r|≤1)
    (softmax : Fin 5 → Bool) (activation : Fin 5 → Fin 6 → Bool)
    (layout : Fin D → FixedTimeLayout (2*D+6) 5 n) (κ R b s0 cκ : ℝ)
    (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0≤κ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs01 : s0≤1) (hcκ : 0≤cκ)
    (hkBudget : κ≤cκ*(D:ℝ)^8*(n:ℝ)^2*b^8*R^4/s0^8)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t ∧ s t≤1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (learn : HierarchicalTrainingSample Θ (CleanPromptSample n D S) (GaussianCoverSample (LegalTime δ) n D S) K J N →
      admissibleFixedTimeParameters (gaussianLossSetup n D (2*D+6) 5 6 n (S:=S) a s (noiseRadius D s0)
        PE tokenMask softmax activation) layout κ R) (hl : Measurable learn) :
    let f := fun θ => fullFixedGaussianDenoisingLoss n D (2*D+6) 5 6 n (S:=S) a s (noiseRadius D s0)
      PE tokenMask softmax activation layout θ.val
    (∫ z, adaptiveHierarchyGap K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) f learn z
      ∂hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) ≤
    statisticalRateConstant cκ b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2 := by
  have hn0 : 0<n := by omega
  have hD0 : 0<D := by omega
  have hw : 0<2*D+6 := by omega
  have h := lemma_two_uniform_time_original δ hδ n D (2*D+6) 5 6 n K J N hn0 hD0 hw hK hJ hN
    S a s ham hsm PE tokenMask hp ht softmax activation layout κ R b s0 hLayout hκ hb hR hs0
    ha hs hbox μTask ρ learn hl
  exact h.trans (lemma_two_bound_rate n D K J N hn hD hK hJ hN κ cκ b R s0 hκ hcκ hb hR hs0 hs01 hkBudget)

#print axioms lemma_two_uniform_time_rate
end GeneralizationCheck
