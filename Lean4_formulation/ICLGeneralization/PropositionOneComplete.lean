module

public import ICLGeneralization.TaskTimeMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 2000000
variable {Θ : Type*} [MeasurableSpace Θ]

/- A measurable task family is represented by a probability kernel. Input Θ
   can contain both a task label and its independently sampled time. -/
noncomputable def candidatePopulationRisk (n D : ℕ) {S : Set (KernelSpace D)}
    (ν : Measure Θ) (ρ : Kernel Θ S) (b R C s0 : ℝ) (a s : Θ → ℝ) : ℝ :=
  ∫ θ, (∫ z : S, (∫ eps, (∫ ω,
    candidateDenoisingLoss n D b R C s0 (a θ) (s θ) ((z,eps),ω)
      ∂promptLaw n (ρ θ)) ∂gaussianNoiseLaw D) ∂ρ θ) ∂ν

noncomputable def oraclePopulationRisk (D : ℕ) {S : Set (KernelSpace D)}
    (ν : Measure Θ) (ρ : Kernel Θ S) (a s : Θ → ℝ) : ℝ :=
  ∫ θ, (∫ z : S, (∫ eps, ∑ j,
    (trueGaussianScore (ρ θ) (a θ) (s θ) (a θ • z.val+s θ • eps) j+eps j/s θ)^2
      ∂gaussianNoiseLaw D) ∂ρ θ) ∂ν

theorem bounded_kernel_expectation {X : Type*} [MeasurableSpace X]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (κ : Kernel Θ X) [IsMarkovKernel κ]
    (f : Θ × X → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ p, |f p| ≤ B) :
    Measurable (fun θ => ∫ x, f (θ,x) ∂κ θ) ∧
    Integrable (fun θ => ∫ x, f (θ,x) ∂κ θ) ν ∧
    (∀ θ, |∫ x, f (θ,x) ∂κ θ| ≤ B) := by
  have hm := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ) |>.measurable
  have hb (θ : Θ) : |∫ x, f (θ,x) ∂κ θ| ≤ B :=
    (bounded_probability_integral (κ θ) _
      (hf.comp ((measurable_const : Measurable (fun _ : X => θ)).prodMk measurable_id))
      B (fun x => hB (θ,x))).2
  exact ⟨hm, (bounded_probability_integral ν _ hm B hb).1, hb⟩

theorem population_risks_episode_representation (n D : ℕ) (S : Set (KernelSpace D))
    (ν : Measure Θ) (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (b R C s0 : ℝ) (a s : Θ → ℝ) (ha : Measurable a) (hs : Measurable s)
    (hb : 0 ≤ b) (haRange : ∀ θ, 0 ≤ a θ ∧ a θ ≤ 1)
    (hs0 : 0 < s0) (hsRange : ∀ θ, s0 ≤ s θ)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) :
    candidatePopulationRisk n D ν ρ b R C s0 a s =
      ∫ θ, (∫ p, candidateDenoisingLoss n D b R C s0 (a θ) (s θ) p
        ∂episodeLaw n D (ρ θ)) ∂ν ∧
    oraclePopulationRisk D ν ρ a s =
      ∫ θ, (∫ p, oracleDenoisingLoss n D (ρ θ) (a θ) (s θ) p
        ∂episodeLaw n D (ρ θ)) ∂ν := by
  have hm := measurable_parameterized_denoising_losses n D S ρ b R C s0 a s ha hs hb
    haRange (fun θ => lt_of_lt_of_le hs0 (hsRange θ)) hbox
  have hc (θ : Θ) : Measurable (candidateDenoisingLoss n D b R C s0 (a θ) (s θ)) :=
    hm.1.comp (f := fun p : EpisodeSample n D S => (θ,p))
      ((measurable_const : Measurable (fun _ : EpisodeSample n D S => θ)).prodMk
        (measurable_id : Measurable (id : EpisodeSample n D S → EpisodeSample n D S)))
  have ho (θ : Θ) : Measurable (oracleDenoisingLoss n D (ρ θ) (a θ) (s θ)) :=
    hm.2.comp (f := fun p : EpisodeSample n D S => (θ,p))
      ((measurable_const : Measurable (fun _ : EpisodeSample n D S => θ)).prodMk
        (measurable_id : Measurable (id : EpisodeSample n D S → EpisodeSample n D S)))
  have hcb (θ : Θ) := fun p => (denoising_loss_uniform_envelope n D S (ρ θ) b R C s0
    (a θ) (s θ) hb (haRange θ) hs0 (hsRange θ) hbox p).1
  have hob (θ : Θ) := fun p => (denoising_loss_uniform_envelope n D S (ρ θ) b R C s0
    (a θ) (s θ) hb (haRange θ) hs0 (hsRange θ) hbox p).2
  constructor
  · unfold candidatePopulationRisk
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun θ =>
      (bounded_episode_integral n D S (ρ θ) _ (hc θ) _ (hcb θ)).symm)
  · unfold oraclePopulationRisk
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro θ
    dsimp only
    rw [bounded_episode_integral n D S (ρ θ) _ (ho θ) _ (hob θ)]
    simp only [oracleDenoisingLoss, episodeQuery, integral_const, probReal_univ, one_smul]

theorem proposition_one_complete (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (S : Set (KernelSpace D)) (hS : IsCompact S)
    (ν : Measure Θ) [IsProbabilityMeasure ν] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (b R A s0 : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (a s : Θ → ℝ) (ha : Measurable a) (hs : Measurable s)
    (haRange : ∀ θ, 0 ≤ a θ ∧ a θ ≤ 1) (hsRange : ∀ θ, s0 ≤ s θ ∧ s θ ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∀ j, InScalarTransformerClass
      (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (approximationWeightBudget n D b R s0)) ∧
    candidatePopulationRisk n D ν ρ b R (noiseRadius D s0) s0 a s-
      oraclePopulationRisk D ν ρ a s ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  constructor
  · intro j
    have hm := lemma_five_candidate_membership n D hD j b R s0 hb hR
    exact ⟨network_budget_mono _ _ _ hm.1
      (lemma_five_weight_budget_order n D hn hD b R s0 hb hR hs0 hs01), hm.2⟩
  · have hb0 : 0 ≤ b := by linarith
    have hm := measurable_parameterized_denoising_losses n D S ρ b R (noiseRadius D s0)
      s0 a s ha hs hb0 haRange (fun θ => lt_of_lt_of_le hs0 (hsRange θ).1) hbox
    have hcb (p : Θ × EpisodeSample n D S) :=
      (denoising_loss_uniform_envelope n D S (ρ p.1) b R (noiseRadius D s0) s0
        (a p.1) (s p.1) hb0 (haRange p.1) hs0 (hsRange p.1).1 hbox p.2).1
    have hob (p : Θ × EpisodeSample n D S) :=
      (denoising_loss_uniform_envelope n D S (ρ p.1) b R (noiseRadius D s0) s0
        (a p.1) (s p.1) hb0 (haRange p.1) hs0 (hsRange p.1).1 hbox p.2).2
    have hc := bounded_kernel_expectation ν (episodeKernel n D ρ) _ hm.1 _ hcb
    have ho := bounded_kernel_expectation ν (episodeKernel n D ρ) _ hm.2 _ hob
    simp only [episode_kernel_apply] at hc ho
    obtain ⟨hcr,hor⟩ := population_risks_episode_representation n D S ν ρ b R (noiseRadius D s0)
      s0 a s ha hs hb0 haRange hs0 (fun θ => (hsRange θ).1) hbox
    rw [hcr, hor, ← integral_sub hc.2.1 ho.2.1]
    have hi := integral_mono_ae (hc.2.1.sub ho.2.1) (integrable_const
      (approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2))
      (Filter.Eventually.of_forall (fun θ => proposition_one_fixed_task_time n D d hn hD
        S hS (ρ θ) b R A s0 (a θ) (s θ) hb hR hA hs0 hs01 (haRange θ)
        (hsRange θ).1 (hsRange θ).2 hbox hcover))
    simpa only [Pi.sub_apply, integral_const, probReal_univ, one_smul] using hi

/- Taking ν = μTask × timeLaw makes the task and time independent. The result
   allows every probability law on legal times, including the paper's uniform law. -/
theorem proposition_one_independent_task_time {Time : Type*} [MeasurableSpace Time]
    (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D) (S : Set (KernelSpace D)) (hS : IsCompact S)
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (timeLaw : Measure Time) [IsProbabilityMeasure timeLaw]
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (b R A s0 : ℝ)
    (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A) (hs0 : 0 < s0) (hs01 : s0 ≤ 1)
    (a s : Time → ℝ) (ha : Measurable a) (hs : Measurable s)
    (haRange : ∀ t, 0 ≤ a t ∧ a t ≤ 1) (hsRange : ∀ t, s0 ≤ s t ∧ s t ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∀ j, InScalarTransformerClass
      (kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b)
      R (approximationWeightBudget n D b R s0)) ∧
    candidatePopulationRisk n D (μTask.prod timeLaw) (ρ.comap Prod.fst measurable_fst)
      b R (noiseRadius D s0) s0 (a ∘ Prod.snd) (s ∘ Prod.snd)-
    oraclePopulationRisk D (μTask.prod timeLaw) (ρ.comap Prod.fst measurable_fst)
      (a ∘ Prod.snd) (s ∘ Prod.snd) ≤
    approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 :=
  proposition_one_complete n D d hn hD S hS (μTask.prod timeLaw)
    (ρ.comap Prod.fst measurable_fst) b R A s0 hb hR hA hs0 hs01 _ _
    (ha.comp measurable_snd) (hs.comp measurable_snd) (fun p => haRange p.2)
    (fun p => hsRange p.2) hbox hcover

#print axioms bounded_kernel_expectation
#print axioms population_risks_episode_representation
#print axioms proposition_one_complete
#print axioms proposition_one_independent_task_time
end GeneralizationCheck
