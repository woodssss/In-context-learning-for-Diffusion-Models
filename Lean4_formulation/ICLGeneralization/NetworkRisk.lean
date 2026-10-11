module

public import ICLGeneralization.NetworkApproximation
public import ICLGeneralization.ProbabilityExpectation

@[expose] public section

open MeasureTheory
namespace GeneralizationCheck

theorem network_mean_approximation_cover_bound (n D J : ℕ) (hn : 0 < n)
    (S : Set (KernelSpace D)) (hS : IsCompact S) (μ : Measure S) [IsProbabilityMeasure μ]
    (b R C s0 a s : ℝ) (hb : 0 ≤ b) (ha : 0 ≤ a ∧ a ≤ 1) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b) (c : Fin J → KernelSpace D)
    (hcover : ∀ x ∈ S, ∃ j, dist x (c j) ≤ s/2) :
    (∫ z : S, (∫ eps, (∫ ω, candidateMeanError n D μ b R C s0 a s (a • z.val+s • eps) ω
      ∂promptLaw n μ) ∂gaussianNoiseLaw D) ∂μ) ≤
      32*Real.exp 1*(D : ℝ)*b^2/(n : ℝ)*(J : ℝ)+
        4*(D : ℝ)*b^2*(gaussianNoiseLaw D {eps | C < ‖eps‖}).toReal := by
  let B := 4*(D : ℝ)*b^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let fc := fun y => ∫ ω, candidateMeanError n D μ b R C s0 a s y ω ∂promptLaw n μ
  let fk := fun y => ∫ ω, kernelModelError n D μ a s y ω ∂promptLaw n μ
  have hc := integrated_bounded_measurable (promptLaw n μ)
    (fun p : KernelSpace D × (Fin n → S) => candidateMeanError n D μ b R C s0 a s p.1 p.2)
    (measurable_candidate_mean_error n D μ b R C s0 a s) B (fun p => by
      rw [abs_of_nonneg (candidate_mean_error_bounds n D μ b R C s0 a s hb hbox p.1 p.2).1]
      exact (candidate_mean_error_bounds n D μ b R C s0 a s hb hbox p.1 p.2).2)
  have hk := integrated_bounded_measurable (promptLaw n μ)
    (fun p : KernelSpace D × (Fin n → S) => kernelModelError n D μ a s p.1 p.2)
    (measurable_kernel_model_error n D μ a s) B (fun p => by
      rw [abs_of_nonneg (kernel_model_error_bounds n D hn μ b hbox a s p.1 p.2).1]
      exact (kernel_model_error_bounds n D hn μ b hbox a s p.1 p.2).2)
  have hnoise : Measurable (fun p : S × KernelSpace D => a • p.1.val+s • p.2) := by fun_prop
  have hcf : Measurable (fun p : S × KernelSpace D => fc (a • p.1.val+s • p.2)) := hc.1.comp hnoise
  have hkf : Measurable (fun p : S × KernelSpace D => fk (a • p.1.val+s • p.2)) := hk.1.comp hnoise
  have hcn := integrated_bounded_measurable (gaussianNoiseLaw D) _ hcf B (fun p => hc.2.2 _)
  have hkn := integrated_bounded_measurable (gaussianNoiseLaw D) _ hkf B (fun p => hk.2.2 _)
  let tail : KernelSpace D → ℝ := fun eps => if C < ‖eps‖ then B else 0
  have hbad : MeasurableSet {eps : KernelSpace D | C < ‖eps‖} := measurableSet_lt measurable_const (by fun_prop)
  have htmeas : Measurable tail := measurable_const.ite hbad measurable_const
  have htbound (eps : KernelSpace D) : |tail eps| ≤ B := by
    unfold tail
    split_ifs <;> simp [abs_of_nonneg hB, hB]
  have htint := (bounded_probability_integral (gaussianNoiseLaw D) tail htmeas B htbound).1
  have htail : (∫ eps, tail eps ∂gaussianNoiseLaw D) = B*(gaussianNoiseLaw D {eps | C < ‖eps‖}).toReal := by
    have he : tail = {eps : KernelSpace D | C < ‖eps‖}.indicator (fun _ => B) := by
      funext eps
      simp [tail, Set.indicator]
    rw [he, integral_indicator_const B hbad]
    simp only [smul_eq_mul, Measure.real, mul_comm]
  have hpoint (z : S) (eps : KernelSpace D) :
      fc (a • z.val+s • eps) ≤ fk (a • z.val+s • eps)+tail eps := by
    have hi := integral_mono_ae (hc.2.1 _) ((hk.2.1 _).add (integrable_const (tail eps)))
      (Filter.Eventually.of_forall (fun ω => candidate_error_pointwise_transfer n D hn μ
        b R C s0 a s hb ha hs0 hs hbox ω z eps))
    simp only [Pi.add_apply] at hi
    rw [integral_add (hk.2.1 _) (integrable_const _), integral_const, probReal_univ, one_smul] at hi
    exact hi
  have hnoiseBound (z : S) : (∫ eps, fc (a • z.val+s • eps) ∂gaussianNoiseLaw D) ≤
      (∫ eps, fk (a • z.val+s • eps) ∂gaussianNoiseLaw D)+
        B*(gaussianNoiseLaw D {eps | C < ‖eps‖}).toReal := by
    have hi := integral_mono_ae (hcn.2.1 z) ((hkn.2.1 z).add htint)
      (Filter.Eventually.of_forall (hpoint z))
    simp only [Pi.add_apply] at hi
    rwa [integral_add (hkn.2.1 z) htint, htail] at hi
  have hcOuter := (bounded_probability_integral μ _ hcn.1 B hcn.2.2).1
  have hkOuter := (bounded_probability_integral μ _ hkn.1 B hkn.2.2).1
  have hfull := integral_mono_ae hcOuter (hkOuter.add (integrable_const _))
    (Filter.Eventually.of_forall hnoiseBound)
  simp only [Pi.add_apply] at hfull
  rw [integral_add hkOuter (integrable_const _), integral_const, probReal_univ, one_smul] at hfull
  have htransport := subtype_clean_noise_query_integral D S μ a s (lt_of_lt_of_le hs0 hs) fk hk.1 B hk.2.2
  rw [htransport] at hfull
  exact hfull.trans (add_le_add (kernel_sampling_cover_bound n D J hn S hS μ b hb hbox
    c a s ha (lt_of_lt_of_le hs0 hs) hcover) (le_refl _))

noncomputable def candidateScore (n D : ℕ) {S : Set (KernelSpace D)} (b R C s0 a s : ℝ)
    (y : KernelSpace D) (ω : Fin n → S) (j : Fin D) : ℝ :=
  -y j/s^2+a/s^2*candidateMean n D b R C s0 a s y ω j

noncomputable def posteriorScore {D : ℕ} {S : Set (KernelSpace D)} (μ : Measure S) (a s : ℝ)
    (y : KernelSpace D) (j : Fin D) : ℝ := -y j/s^2+a/s^2*kernelModelMean μ a s y j

noncomputable def scoreApproximationError (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (b R C s0 a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) : ℝ :=
  ∑ j, (candidateScore n D b R C s0 a s y ω j-posteriorScore μ a s y j)^2

theorem score_approximation_scaling (n D : ℕ) {S : Set (KernelSpace D)} (μ : Measure S)
    (b R C s0 a s : ℝ) (y : KernelSpace D) (ω : Fin n → S) :
    scoreApproximationError n D μ b R C s0 a s y ω =
      a^2/s^4*candidateMeanError n D μ b R C s0 a s y ω := by
  unfold scoreApproximationError candidateScore posteriorScore candidateMeanError
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv]
  ring

#print axioms network_mean_approximation_cover_bound
#print axioms score_approximation_scaling
end GeneralizationCheck
