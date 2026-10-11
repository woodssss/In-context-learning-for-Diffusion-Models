module

public import ICLGeneralization.FullLossMeasurability

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem full_fixed_loss_nonnegative {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (ω : Ω) : 0≤fullFixedTimeLoss S layout θ ω := by
  unfold fullFixedTimeLoss meanSquaredLoss
  positivity

theorem restricted_fixed_loss_le_full {Ω : Type*} {D w L F m ℓ n : ℕ}
    (S : TransformerLossSetup Ω D w L F m ℓ n) (layout : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) (ω : Ω) :
    restrictedFixedTimeLoss S layout θ ω≤fullFixedTimeLoss S layout θ ω := by
  classical
  unfold restrictedFixedTimeLoss restrictedGeneralLoss
  split_ifs
  · exact le_refl _
  · exact full_fixed_loss_nonnegative S layout θ ω

noncomputable def gaussianTailIndicator {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (M C : ℝ) (p : GaussianCoverSample Time n D S) : ℝ :=
  if C<‖p.2.1.2‖ then M else 0

theorem gaussian_tail_indicator_measurable {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (M C : ℝ) :
    Measurable (gaussianTailIndicator (Time:=Time) n D S M C) :=
  measurable_const.ite (measurableSet_lt measurable_const (by fun_prop)) measurable_const

theorem gaussian_tail_indicator_bound {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (M C : ℝ) (hM : 0≤M) : ∀ p : GaussianCoverSample Time n D S, |gaussianTailIndicator n D S M C p|≤M := by
  intro p
  unfold gaussianTailIndicator
  split_ifs <;> simp [abs_of_nonneg hM,hM]

theorem gaussian_tail_indicator_average {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (S : Set (KernelSpace D)) (M C : ℝ) (hM : 0≤M)
    (μTime : Measure Time) [IsProbabilityMeasure μTime] (x : CleanPromptSample n D S) :
    (∫ p, gaussianTailIndicator n D S M C p ∂timeNoiseEpisodeKernel n D S μTime x) =
      M*(gaussianNoiseLaw D {eps | C<‖eps‖}).toReal := by
  rw [time_noise_episode_expectation n D S μTime _ (gaussian_tail_indicator_measurable n D S M C) M
    (gaussian_tail_indicator_bound n D S M C hM)]
  have hs : MeasurableSet {eps : KernelSpace D | C<‖eps‖} := measurableSet_lt measurable_const (by fun_prop)
  have he (t : Time) : (fun eps => gaussianTailIndicator n D S M C (t,((x.1,eps),x.2))) =
      {eps : KernelSpace D | C<‖eps‖}.indicator (fun _ => M) := by
    funext eps
    simp [gaussianTailIndicator,Set.indicator]
  simp_rw [he,integral_indicator_const M hs]
  simp [smul_eq_mul,Measure.real,mul_comm]

theorem gaussian_restriction_episode_tail {Time : Type*} [MeasurableSpace Time]
    (n D w L F m : ℕ) (S : Set (KernelSpace D)) (a s : Time → ℝ) (C M : ℝ) (hM : 0≤M)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (layout : Fin D → FixedTimeLayout w L m) (θ : VectorFixedTimeParameter D w L F m → ℝ)
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (hf : Measurable (fullFixedTimeLoss (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout θ))
    (hc : Measurable (restrictedFixedTimeLoss (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout θ))
    (hb : ∀ p, |fullFixedTimeLoss (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout θ p|≤M)
    (x : CleanPromptSample n D S) :
    (∫ p, fullFixedTimeLoss (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout θ p
      ∂timeNoiseEpisodeKernel n D S μTime x)-
    (∫ p, restrictedFixedTimeLoss (gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation) layout θ p
      ∂timeNoiseEpisodeKernel n D S μTime x) ≤ M*(gaussianNoiseLaw D {eps | C<‖eps‖}).toReal := by
  classical
  let model := gaussianLossSetup n D w L F m (S:=S) a s C PE tokenMask softmax activation
  let f := fullFixedTimeLoss model layout θ
  let g := restrictedFixedTimeLoss model layout θ
  have gb (p) : |g p|≤M := by
    unfold g restrictedFixedTimeLoss restrictedGeneralLoss
    split_ifs
    · exact hb p
    · simpa using hM
  have hpoint (p) : f p≤g p+gaussianTailIndicator n D S M C p := by
    unfold g restrictedFixedTimeLoss restrictedGeneralLoss gaussianTailIndicator
    change f p≤(if ‖p.2.1.2‖≤C then f p else 0)+(if C<‖p.2.1.2‖ then M else 0)
    by_cases h : ‖p.2.1.2‖≤C
    · simp [h,not_lt.mpr h]
    · simp only [h,ite_false,lt_of_not_ge h,ite_true,zero_add]
      exact (le_abs_self _).trans (hb p)
  have fi := (bounded_probability_integral (timeNoiseEpisodeKernel n D S μTime x) f hf M hb).1
  have gi := (bounded_probability_integral (timeNoiseEpisodeKernel n D S μTime x) g hc M gb).1
  have ti := (bounded_probability_integral (timeNoiseEpisodeKernel n D S μTime x) (gaussianTailIndicator (Time:=Time) n D S M C)
    (gaussian_tail_indicator_measurable n D S M C) M (gaussian_tail_indicator_bound n D S M C hM)).1
  have sumI : Integrable (fun p => g p+gaussianTailIndicator n D S M C p) (timeNoiseEpisodeKernel n D S μTime x) := gi.add ti
  have h := integral_mono fi sumI hpoint
  rw [integral_add gi ti,gaussian_tail_indicator_average n D S M C hM μTime x] at h
  linarith

#print axioms full_fixed_loss_nonnegative
#print axioms restricted_fixed_loss_le_full
#print axioms gaussian_tail_indicator_measurable
#print axioms gaussian_tail_indicator_bound
#print axioms gaussian_tail_indicator_average
#print axioms gaussian_restriction_episode_tail
end GeneralizationCheck
