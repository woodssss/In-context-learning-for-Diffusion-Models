module

public import ICLGeneralization.KernelCandidateBridge

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 2000000

noncomputable def paperParameterSet {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (b R s0 : ℝ) (a s : Time → ℝ) : Set (VectorFixedTimeParameter D (embedWidth D) 5 6 n → ℝ) :=
  admissibleFixedTimeParameters
    (gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
      (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation)
    (kernelCandidateLayout n D b R s0) (approximationWeightBudget n D b R s0) R

noncomputable def paperDenoisingLoss {Time : Type*} (n D : ℕ) (S : Set (KernelSpace D))
    (b R s0 : ℝ) (a s : Time → ℝ)
    (θ : VectorFixedTimeParameter D (embedWidth D) 5 6 n → ℝ) : GaussianCoverSample Time n D S → ℝ :=
  fullFixedGaussianDenoisingLoss n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
    (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation (kernelCandidateLayout n D b R s0) θ

theorem paper_loss_measurable_and_bounded {Time : Type*} [MeasurableSpace Time]
    (n D : ℕ) (hn : 0<n) (hD : 1≤D) (S : Set (KernelSpace D))
    (b R s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (a s : Time → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t)
    (hbox : ∀ x∈S, ∀ j, x j∈Set.Icc (-b) b) :
    Measurable (fun p : (paperParameterSet n D S b R s0 a s) × (GaussianCoverSample Time n D S) =>
      paperDenoisingLoss n D S b R s0 a s p.1.val p.2) ∧
    ∀ θ : paperParameterSet n D S b R s0 a s, ∀ p,
      |paperDenoisingLoss n D S b R s0 a s θ.val p|≤lossEnvelope D R b s0 := by
  let model := gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
    (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation
  let layout := kernelCandidateLayout n D b R s0
  let κ := approximationWeightBudget n D b R s0
  have hk1 := approximation_budget_at_least_one n D hn hD b R s0 hb hR hs0 hs1
  have hm := kernel_candidate_membership n D hn hD S b R s0 hb hR hs0 hs1 a s
  have hLayout : ∀ j, (layout j).Bounded κ := hm.1
  have hb0 : 0≤b := by linarith
  have hR0 : 0≤R := by linarith
  have ha' (p : GaussianCoverSample Time n D S) : 0≤model.alpha p ∧ model.alpha p≤1 := ha p.1
  have hs' (p : GaussianCoverSample Time n D S) : s0≤model.sigma p := hs p.1
  have hz (p : GaussianCoverSample Time n D S) (j : Fin D) : |model.clean p j|≤b :=
    abs_le.mpr (hbox _ p.2.1.1.property j)
  have he (θ) (p : GaussianCoverSample Time n D S) : paperDenoisingLoss n D S b R s0 a s θ p=
      fullFixedTimeLoss model layout θ p :=
    full_gaussian_loss_is_DSM n D (embedWidth D) 5 6 n a s (noiseRadius D s0)
      (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation layout θ p
      (ne_of_gt (lt_of_lt_of_le hs0 (hs p.1)))
  constructor
  · have hh := full_fixed_loss_joint_measurable hn model layout κ R b s0 hLayout (by linarith) hR0 hb0 hs0
      (native_pe_bound n D) (fun _ _ => by change |(1:ℝ)|≤1; norm_num) ha' hs' hz
      (measurable_gaussian_raw_input n D S a s ham hsm) (ham.comp measurable_fst) (hsm.comp measurable_fst)
      (fun j => (measurable_clean_coordinate j).comp measurable_snd.fst.fst)
    have he' : (fun p : (paperParameterSet n D S b R s0 a s) × (GaussianCoverSample Time n D S) =>
        paperDenoisingLoss n D S b R s0 a s p.1.val p.2)=
        (fun p => fullFixedTimeLoss model layout p.1.val p.2) := by
      funext p
      exact he p.1.val p.2
    rw [he']
    exact hh
  · intro θ p
    rw [he]
    exact full_fixed_loss_envelope model layout θ.val κ R b s0 θ.property hR0 hb0 hs0 ha' hs' hz p

theorem paper_candidate_population {Time Θ : Type*} [MeasurableSpace Time] [MeasurableSpace Θ]
    (n D : ℕ) (hn : 0<n) (hD : 1≤D) (S : Set (KernelSpace D))
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (b R s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (a s : Time → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t)
    (hbox : ∀ x∈S, ∀ j, x j∈Set.Icc (-b) b) :
    hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
      (paperDenoisingLoss n D S b R s0 a s (kernelCandidateParameter n D b R s0)) =
    candidatePopulationRisk n D (μTask.prod μTime) (ρ.comap Prod.fst measurable_fst)
      b R (noiseRadius D s0) s0 (a ∘ Prod.snd) (s ∘ Prod.snd) := by
  let κ : Kernel (Θ × Time) S := ρ.comap (Prod.fst : Θ × Time → Θ) measurable_fst
  let ν := μTask.prod μTime
  let cand : paperParameterSet n D S b R s0 a s :=
    ⟨kernelCandidateParameter n D b R s0,(kernel_candidate_membership n D hn hD S b R s0 hb hR hs0 hs1 a s).2⟩
  have hprops := paper_loss_measurable_and_bounded n D hn hD S b R s0 hb hR hs0 hs1 a s ham hsm ha hs hbox
  have hf : Measurable (paperDenoisingLoss n D S b R s0 a s (kernelCandidateParameter n D b R s0)) := by
    have hp : Measurable (fun p : GaussianCoverSample Time n D S => (cand,p)) := measurable_const.prodMk measurable_id
    have hc := hprops.1.comp (f:=fun p : GaussianCoverSample Time n D S => (cand,p)) hp
    change Measurable (fun p : GaussianCoverSample Time n D S => paperDenoisingLoss n D S b R s0 a s cand.val p)
    simpa only [Function.comp_def] using hc
  have hb0 : 0≤b := by linarith
  have hm := (measurable_parameterized_denoising_losses n D S κ b R (noiseRadius D s0) s0
    (a ∘ Prod.snd) (s ∘ Prod.snd) (ham.comp measurable_snd) (hsm.comp measurable_snd) hb0
    (fun p => ha p.2) (fun p => lt_of_lt_of_le hs0 (hs p.2)) hbox).1
  have hbnd (p : (Θ × Time) × EpisodeSample n D S) :=
    (denoising_loss_uniform_envelope n D S (κ p.1) b R (noiseRadius D s0) s0
      (a p.1.2) (s p.1.2) hb0 (ha p.1.2) hs0 (hs p.1.2) hbox p.2).1
  have hh := bounded_kernel_expectation ν (episodeKernel n D κ) _ hm _ hbnd
  simp only [episode_kernel_apply] at hh
  have hrep := (population_risks_episode_representation n D S ν κ b R (noiseRadius D s0) s0
    (a ∘ Prod.snd) (s ∘ Prod.snd) (ham.comp measurable_snd) (hsm.comp measurable_snd) hb0
    (fun p => ha p.2) hs0 (fun p => hs p.2) hbox).1
  rw [hrep,integral_prod _ hh.2.1]
  rw [hierarchy_time_episode_population n D S μTask ρ μTime _ hf (lossEnvelope D R b s0) (hprops.2 cand)]
  simp only [paperDenoisingLoss]
  simp_rw [kernel_candidate_loss n D hn S b R s0 a s]
  rfl

#print axioms paper_loss_measurable_and_bounded
#print axioms paper_candidate_population
end GeneralizationCheck
