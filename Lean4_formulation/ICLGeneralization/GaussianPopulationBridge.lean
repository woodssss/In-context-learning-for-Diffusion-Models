module

public import ICLGeneralization.ERMAssembly

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 1000000

theorem clean_prompt_time_noise_population {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S) [IsProbabilityMeasure μ]
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (f : GaussianCoverSample Time n D S → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ p, |f p|≤M) :
    (∫ x, (∫ p, f p ∂timeNoiseEpisodeKernel n D S μTime x) ∂μ.prod (promptLaw n μ)) =
      ∫ t, (∫ p, f (t,p) ∂episodeLaw n D μ) ∂μTime := by
  let h : (CleanPromptSample n D S) × Time → ℝ :=
    fun p => ∫ eps, f (p.2,((p.1.1,eps),p.1.2)) ∂gaussianNoiseLaw D
  have hh : Measurable h := by
    have hjoint : Measurable (fun p : ((CleanPromptSample n D S) × Time) × KernelSpace D =>
        f (p.1.2,((p.1.1.1,p.2),p.1.1.2))) := hf.comp (by fun_prop)
    exact hjoint.stronglyMeasurable.integral_prod_right' |>.measurable
  have hB (p : (CleanPromptSample n D S) × Time) : |h p|≤M :=
    (bounded_probability_integral (gaussianNoiseLaw D) _ (hf.comp (by fun_prop)) M (fun eps => hb _)).2
  simp_rw [time_noise_episode_expectation n D S μTime f hf M hb]
  change (∫ x, (∫ t, h (x,t) ∂μTime) ∂μ.prod (promptLaw n μ)) = _
  rw [integral_integral_swap (bounded_probability_integral
    ((μ.prod (promptLaw n μ)).prod μTime) h hh M hB).1]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  have htx : Measurable (fun x : CleanPromptSample n D S => h (x,t)) :=
    hh.comp (measurable_id.prodMk measurable_const)
  rw [integral_prod _ (bounded_probability_integral (μ.prod (promptLaw n μ)) _ htx M (fun x => hB (x,t))).1]
  have hft : Measurable (fun p : EpisodeSample n D S => f (t,p)) :=
    hf.comp (measurable_const.prodMk measurable_id)
  rw [bounded_episode_integral n D S μ _ hft M (fun p => hb (t,p))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp [h]
  exact integral_integral_swap (bounded_probability_integral ((promptLaw n μ).prod (gaussianNoiseLaw D))
    (fun p => f (t,((x,p.2),p.1))) (hf.comp (by fun_prop)) M (fun p => hb _)).1

theorem hierarchy_time_episode_population {Time Θ : Type*} [MeasurableSpace Time] [MeasurableSpace Θ]
    (n D : ℕ) (S : Set (KernelSpace D))
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (f : GaussianCoverSample Time n D S → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ p, |f p|≤M) :
    hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime) f =
      ∫ θ, (∫ t, (∫ p, f (t,p) ∂episodeLaw n D (ρ θ)) ∂μTime) ∂μTask := by
  unfold hierarchicalPopulationLoss
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro θ
  dsimp only
  rw [clean_prompt_kernel_apply]
  exact clean_prompt_time_noise_population n D S (ρ θ) μTime f hf M hb

#print axioms clean_prompt_time_noise_population
#print axioms hierarchy_time_episode_population
end GeneralizationCheck
