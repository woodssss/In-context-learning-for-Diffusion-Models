module

public import ICLGeneralization.DSMIdentity
public import ICLGeneralization.LemmaFiveComplete
public import ICLGeneralization.ScheduledNetworkMeasurability

@[expose] public section
open MeasureTheory
namespace GeneralizationCheck

noncomputable def candidateDenoisingLoss (n D : ℕ) {S : Set (KernelSpace D)}
    (b R C s0 a s : ℝ) (p : EpisodeSample n D S) : ℝ :=
  ∑ j, (candidateScore n D b R C s0 a s (episodeQuery n D a s p) p.2 j+p.1.2 j/s)^2

noncomputable def oracleDenoisingLoss (n D : ℕ) {S : Set (KernelSpace D)}
    (μ : Measure S) (a s : ℝ) (p : EpisodeSample n D S) : ℝ :=
  ∑ j, (trueGaussianScore μ a s (episodeQuery n D a s p) j+p.1.2 j/s)^2

theorem candidate_denoising_loss_reduction (n D : ℕ) {S : Set (KernelSpace D)}
    (b R C s0 a s : ℝ) (hs : s ≠ 0) (p : EpisodeSample n D S) :
    candidateDenoisingLoss n D b R C s0 a s p =
      a^2/s^4*meanPredictionLoss n D (fun q => candidateMean n D b R C s0 a s q.1 q.2) a s p := by
  unfold candidateDenoisingLoss meanPredictionLoss candidateScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := residual_cancel a s (candidateMean n D b R C s0 a s (episodeQuery n D a s p) p.2 j)
    (p.1.1.val j) (p.1.2 j) hs
  change (-(a*(p.1.1.val j)+s*(p.1.2 j))/s^2+a/s^2*_
    +p.1.2 j/s)^2 = _
  convert congrArg (fun v : ℝ => v^2) h using 1
  all_goals ring

theorem oracle_denoising_loss_reduction (n D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) [IsProbabilityMeasure μ] (b a s : ℝ)
    (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (p : EpisodeSample n D S) :
    oracleDenoisingLoss n D μ a s p = a^2/s^4*meanOracleLoss n D μ a s p := by
  unfold oracleDenoisingLoss meanOracleLoss
  simp_rw [true_gaussian_score_eq_posterior D S μ b a s hb ha hs hbox]
  unfold posteriorScore
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := residual_cancel a s (kernelModelMean μ a s (episodeQuery n D a s p) j)
    (p.1.1.val j) (p.1.2 j) (ne_of_gt hs)
  change (-(a*(p.1.1.val j)+s*(p.1.2 j))/s^2+a/s^2*_
    +p.1.2 j/s)^2 = _
  convert congrArg (fun v : ℝ => v^2) h using 1
  all_goals ring

theorem fixed_task_time_DSM (n D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (b R C s0 a s : ℝ)
    (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) :
    (∫ p, candidateDenoisingLoss n D b R C s0 a s p ∂episodeLaw n D μ)-
      (∫ p, oracleDenoisingLoss n D μ a s p ∂episodeLaw n D μ) =
      ∫ p, scoreApproximationError n D μ b R C s0 a s (episodeQuery n D a s p) p.2
        ∂episodeLaw n D μ := by
  simp_rw [candidate_denoising_loss_reduction n D b R C s0 a s (ne_of_gt hs),
    oracle_denoising_loss_reduction n D S μ b a s hb ha hs hbox,
    score_approximation_scaling]
  apply bounded_mean_DSM_identity n D S μ b a s hb hs hbox
  · intro j
    apply measurable_transformer_eval
    · intro i r
      exact (measurable_clean_coordinate r).comp ((measurable_pi_apply i).comp measurable_snd)
    · intro r
      exact (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) r).measurable.comp measurable_fst
  · intro q j
    exact kernel_transformer_global_bound n D j _ b a s hb _ _

theorem proposition_one_fixed_task_time (n D d : ℕ) (hn : 0 < n) (hD : 1 ≤ D)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R A s0 a s : ℝ) (hb : 1 ≤ b) (hR : b ≤ R) (hA : 0 ≤ A)
    (hs0 : 0 < s0) (hs01 : s0 ≤ 1) (ha : 0 ≤ a ∧ a ≤ 1) (hs : s0 ≤ s) (hs1 : s ≤ 1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (hcover : HasPolynomialBallCovers S d A) :
    (∫ p, candidateDenoisingLoss n D b R (noiseRadius D s0) s0 a s p ∂episodeLaw n D μ)-
      (∫ p, oracleDenoisingLoss n D μ a s p ∂episodeLaw n D μ) ≤
      approximationConstant b d*A*(D : ℝ)/((n : ℝ)*s0^(d+4))+4*(D : ℝ)*b^2*s0^2 := by
  rw [fixed_task_time_DSM n D S μ b R (noiseRadius D s0) s0 a s (by linarith) ha
    (lt_of_lt_of_le hs0 hs) hbox]
  have hf : Measurable (fun p : EpisodeSample n D S =>
      scoreApproximationError n D μ b R (noiseRadius D s0) s0 a s (episodeQuery n D a s p) p.2) := by
    simp_rw [score_approximation_scaling]
    exact (measurable_candidate_mean_error n D μ b R (noiseRadius D s0) s0 a s).comp
      ((measurable_episode_query n D S a s).prodMk measurable_snd) |>.const_mul _
  have hbound (p : EpisodeSample n D S) :
      |scoreApproximationError n D μ b R (noiseRadius D s0) s0 a s (episodeQuery n D a s p) p.2| ≤
        a^2/s^4*(4*(D : ℝ)*b^2) := by
    rw [score_approximation_scaling, abs_mul, abs_of_nonneg (by positivity : 0 ≤ a^2/s^4),
      abs_of_nonneg (candidate_mean_error_bounds n D μ b R (noiseRadius D s0) s0 a s
        (by linarith) hbox _ _).1]
    exact mul_le_mul_of_nonneg_left (candidate_mean_error_bounds n D μ b R (noiseRadius D s0)
      s0 a s (by linarith) hbox _ _).2 (by positivity)
  rw [bounded_episode_integral n D S μ _ hf _ hbound]
  unfold scoreApproximationError
  simp_rw [← true_gaussian_score_eq_posterior D S μ b a s (by linarith) ha
    (lt_of_lt_of_le hs0 hs) hbox]
  exact (lemma_five_complete n D d hn hD S hS μ b R A s0 a s hb hR hA hs0 hs01 ha hs hs1 hbox hcover).2

#print axioms candidate_denoising_loss_reduction
#print axioms oracle_denoising_loss_reduction
#print axioms fixed_task_time_DSM
#print axioms proposition_one_fixed_task_time
end GeneralizationCheck
