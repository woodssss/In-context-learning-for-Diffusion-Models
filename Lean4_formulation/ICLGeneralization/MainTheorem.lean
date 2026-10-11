module

public import ICLGeneralization.MainGeneralization

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 2000000

theorem main_weight_budget_cutoff (n D d : ℕ) (hn : 0<n) (b R : ℝ) :
    approximationWeightBudget n D b R ((n:ℝ)^(-1/((d:ℝ)+6))) =
      41943040*(D:ℝ)^8*(n:ℝ)^((2*(d:ℝ)+20)/((d:ℝ)+6))*b^8*R^4 := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have h := cutoff_weight (n:ℝ) (d:ℝ) hn0 (by positivity)
  unfold approximationWeightBudget
  calc
    _ = 41943040*(D:ℝ)^8*((n:ℝ)^2/((n:ℝ)^(-1/((d:ℝ)+6)))^8)*b^8*R^4 := by ring
    _ = _ := by rw [h]

/- Final manuscript rate for a supplied measurable empirical minimizer.
   The specified cutoff is attained at the left endpoint of the schedule. -/
theorem main_generalization_error {Θ : Type*} [MeasurableSpace Θ]
    (δ : ℝ) (_hδ0 : 0<δ) (hδ : δ<1) (n D d K J N : ℕ) (hn : 2≤n) (hD : 1≤D)
    (hK : 0<K) (hJ : 0<J) (hN : 0<N) (S : Set (KernelSpace D)) (hS : IsCompact S)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (b R A s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hA : 0≤A)
    (hcutoff : s0=(n:ℝ)^(-1/((d:ℝ)+6)))
    (a s : LegalTime δ → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (_hsδ : s ⟨δ,⟨le_rfl,hδ.le⟩⟩=s0)
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
    mainStatisticalConstant b R*(D:ℝ)^(5/2:ℝ)*(n:ℝ)^(1/2+4/((d:ℝ)+6))*
      Real.sqrt (Real.log ((n:ℝ)^2*(D:ℝ)*((K*J)*N:ℝ)))*hierarchicalSamplingFactor K J N+
      mainApproximationConstant b R A d*(D:ℝ)*(n:ℝ)^(-2/((d:ℝ)+6)) := by
  have hnoise := cutoff_positive_and_le_one n d (by omega)
  have hs0 : 0<s0 := by simpa only [hcutoff] using hnoise.1
  have hs1 : s0≤1 := by simpa only [hcutoff] using hnoise.2
  have h := main_generalization_uniform_time δ hδ n D d K J N hn hD hK hJ hN S hS μTask ρ
    b R A s0 hb hR hA hs0 hs1 a s ham hsm ha hs hbox hcover learn hl herm
  apply h.trans
  simpa only [hcutoff] using main_bound_cutoff n D d K J N hn hD hK hJ hN b R A

#print axioms main_weight_budget_cutoff
#print axioms main_generalization_error
end GeneralizationCheck
