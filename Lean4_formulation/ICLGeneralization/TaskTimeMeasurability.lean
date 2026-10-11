module

public import ICLGeneralization.PropositionOneFixed
public import ICLGeneralization.TaskSamplingKernel

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
variable {Θ : Type*} [MeasurableSpace Θ]

noncomputable def episodeKernel (n D : ℕ) {S : Set (KernelSpace D)}
    (ρ : Kernel Θ S) : Kernel Θ (EpisodeSample n D S) :=
  (ρ.prod (Kernel.const Θ (gaussianNoiseLaw D))).prod (iidPromptKernel n ρ)

instance (n D : ℕ) {S : Set (KernelSpace D)} (ρ : Kernel Θ S) [IsMarkovKernel ρ] :
    IsMarkovKernel (episodeKernel n D ρ) := by unfold episodeKernel; infer_instance

theorem episode_kernel_apply (n D : ℕ) {S : Set (KernelSpace D)}
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (θ : Θ) :
    episodeKernel n D ρ θ = episodeLaw n D (ρ θ) := by
  simp only [episodeKernel, Kernel.prod_apply, Kernel.const_apply, iid_prompt_kernel_apply, episodeLaw]

theorem measurable_parameterized_posterior (D : ℕ) (S : Set (KernelSpace D))
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (a s : Θ → ℝ)
    (ha : Measurable a) (hs : Measurable s) (j : Fin D) :
    Measurable (fun q : Θ × KernelSpace D => kernelModelMean (ρ q.1) (a q.1) (s q.1) q.2 j) := by
  let κ : Kernel (Θ × KernelSpace D) S := ρ.comap (Prod.fst : Θ × KernelSpace D → Θ) measurable_fst
  have hw : Measurable (fun p : (Θ × KernelSpace D) × S =>
      sampleWeight (a p.1.1) (s p.1.1) p.1.2 p.2) := by
    unfold sampleWeight kernel
    fun_prop
  have hn := (hw.mul ((measurable_clean_coordinate j).comp measurable_snd)).stronglyMeasurable.integral_kernel_prod_right'
    (κ := κ) |>.measurable
  have hd := hw.stronglyMeasurable.integral_kernel_prod_right' (κ := κ) |>.measurable
  exact hn.div hd

theorem measurable_parameterized_candidate (n D : ℕ) (S : Set (KernelSpace D))
    (b R C s0 : ℝ) (a s : Θ → ℝ) (ha : Measurable a) (hs : Measurable s) (j : Fin D) :
    Measurable (fun p : Θ × EpisodeSample n D S =>
      candidateMean n D b R C s0 (a p.1) (s p.1)
        (episodeQuery n D (a p.1) (s p.1) p.2) p.2.2 j) := by
  apply measurable_scheduled_transformer_eval _ _ _ (ha.comp measurable_fst) (hs.comp measurable_fst)
  · intro i r
    exact (measurable_clean_coordinate r).comp ((measurable_pi_apply i).comp measurable_snd.snd)
  · intro r
    change Measurable (fun p : Θ × EpisodeSample n D S =>
      (a p.1 • p.2.1.1.val+s p.1 • p.2.1.2) r)
    fun_prop

theorem measurable_parameterized_denoising_losses (n D : ℕ) (S : Set (KernelSpace D))
    (ρ : Kernel Θ S) [IsMarkovKernel ρ] (b R C s0 : ℝ) (a s : Θ → ℝ)
    (ha : Measurable a) (hs : Measurable s) (hb : 0 ≤ b)
    (haRange : ∀ θ, 0 ≤ a θ ∧ a θ ≤ 1) (hsPos : ∀ θ, 0 < s θ)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) :
    Measurable (fun p : Θ × EpisodeSample n D S =>
      candidateDenoisingLoss n D b R C s0 (a p.1) (s p.1) p.2) ∧
    Measurable (fun p : Θ × EpisodeSample n D S =>
      oracleDenoisingLoss n D (ρ p.1) (a p.1) (s p.1) p.2) := by
  have hq : Measurable (fun p : Θ × EpisodeSample n D S =>
      episodeQuery n D (a p.1) (s p.1) p.2) := by unfold episodeQuery; fun_prop
  have hz (j : Fin D) : Measurable (fun p : Θ × EpisodeSample n D S => p.2.1.1.val j) :=
    (measurable_clean_coordinate j).comp measurable_snd.fst.fst
  have hm (j : Fin D) : Measurable (fun p : Θ × EpisodeSample n D S =>
      kernelModelMean (ρ p.1) (a p.1) (s p.1) (episodeQuery n D (a p.1) (s p.1) p.2) j) :=
    (measurable_parameterized_posterior D S ρ a s ha hs j).comp (measurable_fst.prodMk hq)
  constructor
  · simp_rw [candidate_denoising_loss_reduction n D b R C s0 _ _ (ne_of_gt (hsPos _))]
    unfold meanPredictionLoss
    exact (((ha.comp measurable_fst).pow_const 2).div ((hs.comp measurable_fst).pow_const 4)).mul
      (Finset.measurable_sum _ (fun j _ =>
        ((measurable_parameterized_candidate n D S b R C s0 a s ha hs j).sub (hz j)).pow_const 2))
  · simp_rw [oracle_denoising_loss_reduction n D S _ b _ _ hb (haRange _) (hsPos _) hbox]
    unfold meanOracleLoss
    exact (((ha.comp measurable_fst).pow_const 2).div ((hs.comp measurable_fst).pow_const 4)).mul
      (Finset.measurable_sum _ (fun j _ => ((hm j).sub (hz j)).pow_const 2))

theorem denoising_loss_uniform_envelope (n D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) [IsProbabilityMeasure μ] (b R C s0 a s : ℝ)
    (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (p : EpisodeSample n D S) :
    |candidateDenoisingLoss n D b R C s0 a s p| ≤ 4*(D : ℝ)*b^2/s0^4 ∧
    |oracleDenoisingLoss n D μ a s p| ≤ 4*(D : ℝ)*b^2/s0^4 := by
  have hsp := lt_of_lt_of_le hs0 hs
  have ha2 : a^2 ≤ 1 := by nlinarith [ha.1, ha.2]
  have hf : a^2/s^4 ≤ 1/s0^4 :=
    (div_le_div_of_nonneg_right ha2 (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hs0.le hs 4))
  have squareBound (u v : Fin D → ℝ) (hu : ∀ j, u j ∈ Set.Icc (-b) b) (hv : ∀ j, v j ∈ Set.Icc (-b) b) :
      |∑ j, (u j-v j)^2| ≤ 4*(D : ℝ)*b^2 := by
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact (vector_error_bound D u v b b hu hv).trans_eq (by ring)
  have scaledBound (v : ℝ) (hv : |v| ≤ 4*(D : ℝ)*b^2) : |a^2/s^4*v| ≤ 4*(D : ℝ)*b^2/s0^4 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a^2/s^4)]
    exact (mul_le_mul hf hv (abs_nonneg _) (by positivity)).trans_eq (by ring)
  constructor
  · rw [candidate_denoising_loss_reduction n D b R C s0 a s (ne_of_gt hsp)]
    exact scaledBound _ (squareBound _ _
      (fun j => kernel_transformer_global_bound n D j _ b a s hb _ _)
      (fun j => hbox _ p.1.1.property j))
  · rw [oracle_denoising_loss_reduction n D S μ b a s hb ha hsp hbox]
    exact scaledBound _ (squareBound _ _ (kernel_model_mean_bounds μ b hbox a s _)
      (fun j => hbox _ p.1.1.property j))

#print axioms episode_kernel_apply
#print axioms measurable_parameterized_posterior
#print axioms measurable_parameterized_candidate
#print axioms measurable_parameterized_denoising_losses
#print axioms denoising_loss_uniform_envelope
end GeneralizationCheck
