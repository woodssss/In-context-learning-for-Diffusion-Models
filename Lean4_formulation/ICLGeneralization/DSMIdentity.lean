module

public import ICLGeneralization.DSMOrthogonality

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

abbrev EpisodeSample (n D : ℕ) (S : Set (KernelSpace D)) := (S × KernelSpace D) × (Fin n → S)

noncomputable def episodeLaw (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S) :
    Measure (EpisodeSample n D S) := (μ.prod (gaussianNoiseLaw D)).prod (promptLaw n μ)

instance (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (episodeLaw n D μ) := by unfold episodeLaw; infer_instance

noncomputable def episodeQuery (n D : ℕ) {S : Set (KernelSpace D)} (a s : ℝ)
    (p : EpisodeSample n D S) : KernelSpace D := a • p.1.1.val+s • p.1.2

theorem measurable_episode_query (n D : ℕ) (S : Set (KernelSpace D)) (a s : ℝ) :
    Measurable (episodeQuery n D (S := S) a s) := by unfold episodeQuery; fun_prop

theorem bounded_episode_integral (n D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (f : EpisodeSample n D S → ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀ p, |f p| ≤ B) :
    (∫ p, f p ∂episodeLaw n D μ) =
      ∫ z : S, (∫ eps, (∫ ω, f ((z,eps),ω) ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ := by
  have hi := (bounded_probability_integral (episodeLaw n D μ) f hf B hB).1
  have hmean := integrated_bounded_measurable (promptLaw n μ) f hf B hB
  have hm := (bounded_probability_integral (μ.prod (gaussianNoiseLaw D)) _ hmean.1 B hmean.2.2).1
  change (∫ p, f p ∂(μ.prod (gaussianNoiseLaw D)).prod (promptLaw n μ)) = _
  rw [integral_prod f hi, integral_prod _ hm]

noncomputable def meanPredictionLoss (n D : ℕ) {S : Set (KernelSpace D)}
    (G : KernelSpace D × (Fin n → S) → Fin D → ℝ) (a s : ℝ) (p : EpisodeSample n D S) : ℝ :=
  ∑ j, (G (episodeQuery n D a s p,p.2) j-p.1.1.val j)^2

noncomputable def meanOracleLoss (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (a s : ℝ) (p : EpisodeSample n D S) : ℝ :=
  ∑ j, (kernelModelMean μ a s (episodeQuery n D a s p) j-p.1.1.val j)^2

noncomputable def meanPredictionError (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (G : KernelSpace D × (Fin n → S) → Fin D → ℝ) (a s : ℝ) (p : EpisodeSample n D S) : ℝ :=
  ∑ j, (G (episodeQuery n D a s p,p.2) j-kernelModelMean μ a s (episodeQuery n D a s p) j)^2

noncomputable def meanCrossCoordinate (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (G : KernelSpace D × (Fin n → S) → Fin D → ℝ) (a s : ℝ) (j : Fin D) (p : EpisodeSample n D S) : ℝ :=
  (G (episodeQuery n D a s p,p.2) j-kernelModelMean μ a s (episodeQuery n D a s p) j)*
    (kernelModelMean μ a s (episodeQuery n D a s p) j-p.1.1.val j)

theorem mean_loss_expansion (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (G : KernelSpace D × (Fin n → S) → Fin D → ℝ) (a s : ℝ) (p : EpisodeSample n D S) :
    meanPredictionLoss n D G a s p-meanOracleLoss n D μ a s p =
      meanPredictionError n D μ G a s p+2*∑ j, meanCrossCoordinate n D μ G a s j p := by
  unfold meanPredictionLoss meanOracleLoss meanPredictionError meanCrossCoordinate
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem bounded_mean_DSM_identity (n D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (b a s : ℝ) (hb : 0 ≤ b) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (G : KernelSpace D × (Fin n → S) → Fin D → ℝ)
    (hG : ∀ j, Measurable (fun q => G q j))
    (hGb : ∀ q j, G q j ∈ Set.Icc (-b) b) :
    (∫ p, a^2/s^4*meanPredictionLoss n D G a s p ∂episodeLaw n D μ)-
      (∫ p, a^2/s^4*meanOracleLoss n D μ a s p ∂episodeLaw n D μ) =
      ∫ p, a^2/s^4*meanPredictionError n D μ G a s p ∂episodeLaw n D μ := by
  have hm (j : Fin D) : Measurable (fun p : EpisodeSample n D S =>
      kernelModelMean μ a s (episodeQuery n D a s p) j) :=
    (measurable_kernel_model_mean μ a s j).comp (measurable_episode_query n D S a s)
  have hg (j : Fin D) : Measurable (fun p : EpisodeSample n D S => G (episodeQuery n D a s p,p.2) j) :=
    (hG j).comp ((measurable_episode_query n D S a s).prodMk measurable_snd)
  have hz (j : Fin D) : Measurable (fun p : EpisodeSample n D S => p.1.1.val j) :=
    (measurable_clean_coordinate j).comp measurable_fst.fst
  have hL : Measurable (meanPredictionLoss n D G a s) :=
    Finset.measurable_sum _ (fun j _ => ((hg j).sub (hz j)).pow_const 2)
  have hO : Measurable (meanOracleLoss n D μ a s) :=
    Finset.measurable_sum _ (fun j _ => ((hm j).sub (hz j)).pow_const 2)
  have hE : Measurable (meanPredictionError n D μ G a s) :=
    Finset.measurable_sum _ (fun j _ => ((hg j).sub (hm j)).pow_const 2)
  have hM (p : EpisodeSample n D S) (j : Fin D) :
      kernelModelMean μ a s (episodeQuery n D a s p) j ∈ Set.Icc (-b) b :=
    kernel_model_mean_bounds μ b hbox a s _ j
  have hZ (p : EpisodeSample n D S) (j : Fin D) : p.1.1.val j ∈ Set.Icc (-b) b := hbox _ p.1.1.property j
  have squareBound (u v : Fin D → ℝ) (hu : ∀ j, u j ∈ Set.Icc (-b) b) (hv : ∀ j, v j ∈ Set.Icc (-b) b) :
      |∑ j, (u j-v j)^2| ≤ 4*(D : ℝ)*b^2 := by
    rw [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    exact (vector_error_bound D u v b b hu hv).trans_eq (by ring)
  have hiL := (bounded_probability_integral (episodeLaw n D μ) _ hL _
    (fun p => squareBound _ _ (hGb _) (hZ p))).1
  have hiO := (bounded_probability_integral (episodeLaw n D μ) _ hO _
    (fun p => squareBound _ _ (hM p) (hZ p))).1
  have hiE := (bounded_probability_integral (episodeLaw n D μ) _ hE _
    (fun p => squareBound _ _ (hGb _) (hM p))).1
  have hCmeas (j : Fin D) : Measurable (meanCrossCoordinate n D μ G a s j) :=
    ((hg j).sub (hm j)).mul ((hm j).sub (hz j))
  have hCbound (j : Fin D) (p : EpisodeSample n D S) : |meanCrossCoordinate n D μ G a s j p| ≤ 4*b^2 := by
    have h1 : |G (episodeQuery n D a s p,p.2) j-kernelModelMean μ a s (episodeQuery n D a s p) j| ≤ 2*b := by
      apply abs_le.mpr
      constructor <;> linarith [(hGb (episodeQuery n D a s p,p.2) j).1, (hGb (episodeQuery n D a s p,p.2) j).2, (hM p j).1, (hM p j).2]
    have h2 := posterior_clean_residual_bound D S μ b a s hb hbox (episodeQuery n D a s p) p.1.1 j
    rw [meanCrossCoordinate, abs_mul]
    exact (mul_le_mul h1 h2 (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hiC (j : Fin D) := (bounded_probability_integral (episodeLaw n D μ) _ (hCmeas j) _ (hCbound j)).1
  have hCzero (j : Fin D) : (∫ p, meanCrossCoordinate n D μ G a s j p ∂episodeLaw n D μ)=0 := by
    rw [bounded_episode_integral n D S μ _ (hCmeas j) _ (hCbound j)]
    apply independent_prompt_coordinate_orthogonality n D S μ b a s hb hs hbox j
      (fun q => G q j-kernelModelMean μ a s q.1 j)
      ((hG j).sub ((measurable_kernel_model_mean μ a s j).comp measurable_fst)) (2*b)
    intro q
    have h := kernel_model_mean_bounds μ b hbox a s q.1 j
    apply abs_le.mpr
    constructor <;> linarith [(hGb q j).1, (hGb q j).2, h.1, h.2]
  have hiSum : Integrable (fun p => ∑ j, meanCrossCoordinate n D μ G a s j p) (episodeLaw n D μ) :=
    integrable_finsetSum _ (fun j _ => hiC j)
  have hsumzero : (∫ p, ∑ j, meanCrossCoordinate n D μ G a s j p ∂episodeLaw n D μ)=0 := by
    rw [integral_finsetSum _ (fun j _ => hiC j)]
    simp_rw [hCzero]
    simp
  simp_rw [integral_const_mul]
  rw [← mul_sub]
  congr 1
  rw [← integral_sub hiL hiO]
  calc
    _ = ∫ p, meanPredictionError n D μ G a s p+2*∑ j, meanCrossCoordinate n D μ G a s j p ∂episodeLaw n D μ :=
      integral_congr_ae (Filter.Eventually.of_forall (mean_loss_expansion n D μ G a s))
    _ = _ := by rw [integral_add hiE (hiSum.const_mul 2), integral_const_mul, hsumzero]; ring

#print axioms measurable_episode_query
#print axioms bounded_episode_integral
#print axioms mean_loss_expansion
#print axioms bounded_mean_DSM_identity
end GeneralizationCheck
