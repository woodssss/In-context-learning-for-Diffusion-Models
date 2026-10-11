module

public import ICLGeneralization.GaussianERMSetup
public import ICLGeneralization.MainRateAlgebra

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 2000000

/- The learner's measurability and exact empirical optimality are explicit
   premises. The statistical and approximation estimates are derived here. -/
theorem main_generalization_uniform_time {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (hδ : δ<1) (n D d K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (S : Set (KernelSpace D)) (hS : IsCompact S)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (b R A s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hA : 0≤A) (hs0 : 0<s0) (hs1 : s0≤1)
    (a s : LegalTime δ → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t ∧ s t≤1)
    (hbox : ∀ x∈S, ∀ j, x j∈Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A)
    (learn : HierarchicalTrainingSample Θ (CleanPromptSample n D S) (GaussianCoverSample (LegalTime δ) n D S) K J N →
      paperParameterSet n D S b R s0 a s) (hl : Measurable learn)
    (herm : ∀ z, ∀ θ : paperParameterSet n D S b R s0 a s,
      hierarchicalEmpiricalLoss K J N (paperDenoisingLoss n D S b R s0 a s (learn z).val) z≤
      hierarchicalEmpiricalLoss K J N (paperDenoisingLoss n D S b R s0 a s θ.val) z) :
    (∫ z, hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ)
        (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))
        (paperDenoisingLoss n D S b R s0 a s (learn z).val)-
      oraclePopulationRisk D (μTask.prod (uniformTimeLaw δ)) (ρ.comap Prod.fst measurable_fst)
        (a ∘ Prod.snd) (s ∘ Prod.snd)
      ∂hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) ≤
    statisticalRateConstant 41943040 b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2+
      (approximationConstant b d*A*(D:ℝ)/((n:ℝ)*s0^(d+4))+4*(D:ℝ)*b^2*s0^2) := by
  let : Fact (δ<1) := ⟨hδ⟩
  have hn0 : 0<n := by omega
  let κ := approximationWeightBudget n D b R s0
  let layout := kernelCandidateLayout n D b R s0
  let f := fun θ : paperParameterSet n D S b R s0 a s => paperDenoisingLoss n D S b R s0 a s θ.val
  let oracle := oraclePopulationRisk D (μTask.prod (uniformTimeLaw δ)) (ρ.comap Prod.fst measurable_fst)
    (a ∘ Prod.snd) (s ∘ Prod.snd)
  have hmember := kernel_candidate_membership n D hn0 hD S b R s0 hb hR hs0 hs1 a s
  let cand : paperParameterSet n D S b R s0 a s := ⟨kernelCandidateParameter n D b R s0,hmember.2⟩
  have hprops := paper_loss_measurable_and_bounded n D hn0 hD S b R s0 hb hR hs0 hs1 a s ham hsm
    ha (fun t => (hs t).1) hbox
  have hdecomp := erm_expected_excess K J N hK hJ hN μTask (cleanPromptKernel n D ρ)
    (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) f hprops.1 (lossEnvelope D R b s0) hprops.2
    learn hl herm cand oracle
  have hk1 := approximation_budget_at_least_one n D hn0 hD b R s0 hb hR hs0 hs1
  have hRate := lemma_two_uniform_time_rate (Θ:=Θ) δ hδ n D K J N hn hD hK hJ hN S a s ham hsm
  rw [←flat_embedding_dimension D] at hRate
  have hstat := hRate (nativePE n D) (fun _ _ => 1) (native_pe_bound n D) (fun _ _ => by norm_num)
    nativeSoftmax nativeActivation layout κ R b s0 41943040 hmember.1 (by linarith)
    hb hR hs0 hs1 (by norm_num) (le_refl _) ha hs hbox μTask ρ learn hl
  change (∫ z, adaptiveHierarchyGap K J N μTask (cleanPromptKernel n D ρ)
      (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) f learn z
      ∂hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ)
        (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ))) ≤
    statisticalRateConstant 41943040 b R*lossEnvelope D R b s0*
      Real.sqrt ((n:ℝ)*(D:ℝ)^3*Real.log ((n:ℝ)*(D:ℝ)*((K*J)*N:ℝ)/s0))*hierarchicalSamplingFactor K J N+
      (D:ℝ)*(R+b)^2*s0^2 at hstat
  have hcPop := paper_candidate_population n D hn0 hD S μTask ρ (uniformTimeLaw δ) b R s0
    hb hR hs0 hs1 a s ham hsm ha (fun t => (hs t).1) hbox
  have happrox := (proposition_one_uniform_time n D d hn0 hD S hS μTask ρ b R A s0 δ hδ
    hb hR hA hs0 hs1 a s ham hsm ha hs hbox hcover).2
  have hAp : hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ)
      (timeNoiseEpisodeKernel n D S (uniformTimeLaw δ)) (f cand)-oracle ≤
      approximationConstant b d*A*(D:ℝ)/((n:ℝ)*s0^(d+4))+4*(D:ℝ)*b^2*s0^2 := by
    rw [hcPop]
    exact happrox
  have hout := add_le_add hstat hAp
  exact hdecomp.trans (by convert hout using 1; ring)

#print axioms main_generalization_uniform_time
end GeneralizationCheck
