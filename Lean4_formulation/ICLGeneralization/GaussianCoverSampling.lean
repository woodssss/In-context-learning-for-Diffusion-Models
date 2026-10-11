module

public import ICLGeneralization.RestrictedGaussianInput

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

abbrev CleanPromptSample (n D : ℕ) (S : Set (KernelSpace D)) := S × (Fin n → S)

noncomputable def attachTimeNoise {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (p : CleanPromptSample n D S × (Time × KernelSpace D)) : GaussianCoverSample Time n D S :=
  (p.2.1,((p.1.1,p.2.2),p.1.2))

theorem measurable_attach_time_noise {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) : Measurable (attachTimeNoise (Time := Time) n D S) := by
  unfold attachTimeNoise
  fun_prop

noncomputable def timeNoiseEpisodeKernel {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (μTime : Measure Time) :
    Kernel (CleanPromptSample n D S) (GaussianCoverSample Time n D S) :=
  ((Kernel.id : Kernel (CleanPromptSample n D S) (CleanPromptSample n D S)).prod
    (Kernel.const (CleanPromptSample n D S) (μTime.prod (gaussianNoiseLaw D)))).map (attachTimeNoise n D S)

instance {Time : Type*} [MeasurableSpace Time] (n D : ℕ) (S : Set (KernelSpace D))
    (μTime : Measure Time) [IsProbabilityMeasure μTime] : IsMarkovKernel (timeNoiseEpisodeKernel n D S μTime) :=
  Kernel.IsMarkovKernel.map _ (measurable_attach_time_noise n D S)

noncomputable def cleanPromptKernel {Θ : Type*} [MeasurableSpace Θ]
    (n D : ℕ) {S : Set (KernelSpace D)} (ρ : Kernel Θ S) : Kernel Θ (CleanPromptSample n D S) :=
  ρ.prod (iidPromptKernel n ρ)

instance {Θ : Type*} [MeasurableSpace Θ] (n D : ℕ) {S : Set (KernelSpace D)}
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] : IsMarkovKernel (cleanPromptKernel n D ρ) := by
  unfold cleanPromptKernel
  infer_instance

theorem clean_prompt_kernel_apply {Θ : Type*} [MeasurableSpace Θ] (n D : ℕ) {S : Set (KernelSpace D)}
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (θ : Θ) : cleanPromptKernel n D ρ θ = (ρ θ).prod (promptLaw n (ρ θ)) := by
  simp only [cleanPromptKernel,Kernel.prod_apply,iid_prompt_kernel_apply]

theorem time_noise_episode_expectation {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (f : GaussianCoverSample Time n D S → ℝ) (hf : Measurable f) (B : ℝ) (hb : ∀ p, |f p| ≤ B)
    (x : CleanPromptSample n D S) :
    (∫ p, f p ∂timeNoiseEpisodeKernel n D S μTime x) =
      ∫ t, (∫ eps, f (t,((x.1,eps),x.2)) ∂gaussianNoiseLaw D) ∂μTime := by
  rw [timeNoiseEpisodeKernel,Kernel.map_apply _ (measurable_attach_time_noise n D S),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,
    integral_map (measurable_attach_time_noise n D S).aemeasurable hf.aestronglyMeasurable]
  have hi := (bounded_probability_integral ((Measure.dirac x).prod (μTime.prod (gaussianNoiseLaw D)))
    (fun p => f (attachTimeNoise n D S p)) (hf.comp (measurable_attach_time_noise n D S)) B (fun p => hb _)).1
  rw [integral_prod _ hi,integral_dirac]
  have ht : Measurable (fun p : Time × KernelSpace D => f (p.1,((x.1,p.2),x.2))) := by
    exact hf.comp (by fun_prop)
  have hi' := (bounded_probability_integral (μTime.prod (gaussianNoiseLaw D)) _ ht B (fun p => hb _)).1
  exact integral_prod _ hi'

theorem clean_prompt_expectation {Θ : Type*} [MeasurableSpace Θ] (n D : ℕ) (S : Set (KernelSpace D))
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (θ : Θ) (f : CleanPromptSample n D S → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ p, |f p| ≤ B) :
    (∫ p, f p ∂cleanPromptKernel n D ρ θ) = ∫ z : S, (∫ ω, f (z,ω) ∂promptLaw n (ρ θ)) ∂ρ θ := by
  rw [clean_prompt_kernel_apply]
  exact integral_prod f ((bounded_probability_integral ((ρ θ).prod (promptLaw n (ρ θ))) f hf B hb).1)

#print axioms measurable_attach_time_noise
#print axioms clean_prompt_kernel_apply
#print axioms time_noise_episode_expectation
#print axioms clean_prompt_expectation
end GeneralizationCheck
