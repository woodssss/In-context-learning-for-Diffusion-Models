module

public import ICLGeneralization.LemmaFiveComplete

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem bounded_support_gaussian_joint_integrable (D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) [IsProbabilityMeasure μ] (a β : ℝ) (hβ : 0 < β)
    (f : S × KernelSpace D → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ p, |f p| ≤ C) :
    Integrable (fun p : S × KernelSpace D => f p*kernel β p.2 (a • p.1.val)) (μ.prod volume) := by
  let F := fun p : S × KernelSpace D => f p*kernel β p.2 (a • p.1.val)
  have hF : Measurable F := by unfold F kernel; fun_prop
  have hnorm (x : S) (y : KernelSpace D) : ‖F (x,y)‖ ≤ C*kernel β y (a • x.val) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < kernel β y (a • x.val) from Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (hC (x,y)) (Real.exp_pos _).le
  have hslice (x : S) : Integrable (fun y => F (x,y)) :=
    ((gaussian_kernel_integrable D β hβ (a • x.val)).const_mul C).mono'
      (hF.comp ((measurable_const : Measurable (fun _ : KernelSpace D => x)).prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hnorm x))
  apply (integrable_prod_iff hF.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall hslice, ?_⟩
  apply (bounded_real_memLp μ _ hF.stronglyMeasurable.norm.integral_prod_right'.measurable
    (C*gaussianNormalizer D β) _ 1).integrable (le_refl _)
  intro x
  rw [abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  have h := integral_mono_ae (hslice x).norm ((gaussian_kernel_integrable D β hβ (a • x.val)).const_mul C)
    (Filter.Eventually.of_forall (hnorm x))
  rwa [integral_const_mul, gaussian_kernel_integral D β hβ (a • x.val)] at h

theorem posterior_clean_residual_bound (D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (b a s : ℝ) (_hb : 0 ≤ b)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (y : KernelSpace D) (z : S) (j : Fin D) :
    |kernelModelMean μ a s y j-z.val j| ≤ 2*b := by
  have hm := kernel_model_mean_bounds μ b hbox a s y j
  have hz := hbox z.val z.property j
  apply abs_le.mpr
  constructor <;> linarith [hm.1, hm.2, hz.1, hz.2]

theorem posterior_coordinate_orthogonality (D : ℕ) (S : Set (KernelSpace D)) (μ : Measure S)
    [IsProbabilityMeasure μ] (b a s : ℝ) (hb : 0 ≤ b) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (j : Fin D)
    (g : KernelSpace D → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ y, |g y| ≤ C) :
    (∫ z : S, (∫ eps, g (a • z.val+s • eps)*
      (kernelModelMean μ a s (a • z.val+s • eps) j-z.val j) ∂gaussianNoiseLaw D) ∂μ) = 0 := by
  let f := fun p : S × KernelSpace D => g p.2*(kernelModelMean μ a s p.2 j-p.1.val j)
  have hC0 : 0 ≤ C := (abs_nonneg (g 0)).trans (hC 0)
  have hf : Measurable f := (hg.comp measurable_snd).mul
    (((measurable_kernel_model_mean μ a s j).comp measurable_snd).sub
      ((measurable_clean_coordinate j).comp measurable_fst))
  have hbound (p : S × KernelSpace D) : |f p| ≤ C*(2*b) := by
    rw [abs_mul]
    exact mul_le_mul (hC p.2) (posterior_clean_residual_bound D S μ b a s hb hbox p.2 p.1 j)
      (abs_nonneg _) hC0
  have hi := bounded_support_gaussian_joint_integrable D S μ a (1/(2*s^2)) (by positivity) f hf _ hbound
  have hchange (z : S) := noisy_query_single_integral D a s hs z.val
    (fun y => g y*(kernelModelMean μ a s y j-z.val j))
  simp_rw [hchange]
  rw [integral_div]
  have hswap := integral_integral_swap (f := fun (z : S) (y : KernelSpace D) =>
    f (z,y)*kernel (1/(2*s^2)) y (a • z.val)) hi
  change (∫ z : S, (∫ y, f (z,y)*kernel (1/(2*s^2)) y (a • z.val)) ∂μ)/gaussianNormalizer D (1/(2*s^2))=0
  rw [hswap]
  have hzero (y : KernelSpace D) : (∫ z : S, f (z,y)*kernel (1/(2*s^2)) y (a • z.val) ∂μ)=0 := by
    have hw := (bounded_real_memLp μ (sampleWeight a s y) (measurable_fixed_sample_weight a s y) 1
      (fun x => by rw [abs_of_pos (sample_weight_bounds a s y x).1]; exact (sample_weight_bounds a s y x).2) 2).integrable (by norm_num)
    have hwx : Integrable (fun z : S => sampleWeight a s y z*z.val j) μ := by
      apply (bounded_real_memLp μ _ ((measurable_fixed_sample_weight a s y).mul (measurable_clean_coordinate j)) b _ 1).integrable (le_refl _)
      intro z
      change |sampleWeight a s y z*z.val j| ≤ b
      rw [abs_mul, abs_of_pos (sample_weight_bounds a s y z).1]
      exact (mul_le_mul (sample_weight_bounds a s y z).2 (abs_le.mpr (hbox z.val z.property j))
        (abs_nonneg _) (by norm_num)).trans_eq (by ring)
    have hz := centered_kernel_integral_zero μ (sampleWeight a s y) (fun z : S => z.val j) hw hwx
      (ne_of_gt (positive_population_weight μ _ hw (fun z => (sample_weight_bounds a s y z).1)))
    have he (z : S) : f (z,y)*kernel (1/(2*s^2)) y (a • z.val) =
        (-g y)*(sampleWeight a s y z*(z.val j-kernelModelMean μ a s y j)) := by
      dsimp [f, sampleWeight]
      ring
    simp_rw [he]
    rw [integral_const_mul]
    exact mul_eq_zero_of_right _ hz
  simp_rw [hzero]
  simp

theorem independent_prompt_coordinate_orthogonality (n D : ℕ) (S : Set (KernelSpace D))
    (μ : Measure S) [IsProbabilityMeasure μ] (b a s : ℝ) (hb : 0 ≤ b) (hs : 0 < s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (j : Fin D)
    (g : KernelSpace D × (Fin n → S) → ℝ) (hg : Measurable g) (C : ℝ)
    (hC : ∀ p, |g p| ≤ C) :
    (∫ z : S, (∫ eps, (∫ ω, g (a • z.val+s • eps,ω)*
      (kernelModelMean μ a s (a • z.val+s • eps) j-z.val j) ∂promptLaw n μ)
      ∂gaussianNoiseLaw D) ∂μ) = 0 := by
  let f : (S × KernelSpace D) × (Fin n → S) → ℝ :=
    fun p => g (a • p.1.1.val+s • p.1.2,p.2)*
      (kernelModelMean μ a s (a • p.1.1.val+s • p.1.2) j-p.1.1.val j)
  have hC0 : 0 ≤ C := by
    have : Nonempty (Fin n → S) := nonempty_of_isProbabilityMeasure (promptLaw n μ)
    obtain ⟨ω⟩ := this
    exact (abs_nonneg (g (0,ω))).trans (hC (0,ω))
  have hf : Measurable f := by
    apply Measurable.mul
    · exact hg.comp ((by fun_prop : Measurable (fun p : (S × KernelSpace D) × (Fin n → S) =>
        a • p.1.1.val+s • p.1.2)).prodMk measurable_snd)
    · exact ((measurable_kernel_model_mean μ a s j).comp (by fun_prop)).sub
        ((measurable_clean_coordinate j).comp (measurable_fst.fst))
  have hfBound (p : (S × KernelSpace D) × (Fin n → S)) : |f p| ≤ C*(2*b) := by
    rw [abs_mul]
    exact mul_le_mul (hC _) (posterior_clean_residual_bound D S μ b a s hb hbox _ p.1.1 j)
      (abs_nonneg _) hC0
  have hi := (bounded_probability_integral ((μ.prod (gaussianNoiseLaw D)).prod (promptLaw n μ))
    f hf (C*(2*b)) hfBound).1
  have hmean := integrated_bounded_measurable (promptLaw n μ) f hf _ hfBound
  have houter := (bounded_probability_integral (μ.prod (gaussianNoiseLaw D)) _ hmean.1 _ hmean.2.2).1
  rw [← integral_prod _ houter, integral_integral_swap hi]
  have hzero (ω : Fin n → S) : (∫ p, f (p,ω) ∂μ.prod (gaussianNoiseLaw D))=0 := by
    have hislice := (bounded_probability_integral (μ.prod (gaussianNoiseLaw D)) _
      (hf.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : S × KernelSpace D => ω))))
      _ (fun p => hfBound (p,ω))).1
    change Integrable (fun p => f (p,ω)) (μ.prod (gaussianNoiseLaw D)) at hislice
    rw [integral_prod _ hislice]
    exact posterior_coordinate_orthogonality D S μ b a s hb hs hbox j (fun y => g (y,ω))
      (hg.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : KernelSpace D => ω))))
      C (fun y => hC (y,ω))
  simp_rw [hzero]
  simp

#print axioms bounded_support_gaussian_joint_integrable
#print axioms posterior_clean_residual_bound
#print axioms posterior_coordinate_orthogonality
#print axioms independent_prompt_coordinate_orthogonality
end GeneralizationCheck
