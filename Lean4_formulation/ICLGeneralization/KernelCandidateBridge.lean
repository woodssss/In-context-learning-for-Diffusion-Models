module

public import ICLGeneralization.GaussianPopulationBridge
public import ICLGeneralization.NativeCoverMembership

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck
set_option maxHeartbeats 1000000

noncomputable def kernelCandidateFamily (n D : ℕ) (b R s0 : ℝ) : Fin D → FiveBlockTransformer n D :=
  fun j => kernelTransformer n D j (realizationM D b R s0 (noiseRadius D s0)) b

noncomputable def kernelCandidateLayout (n D : ℕ) (b R s0 : ℝ) : Fin D → FixedTimeLayout (embedWidth D) 5 n :=
  fun j => nativeLayout (kernelCandidateFamily n D b R s0 j)

noncomputable def kernelCandidateParameter (n D : ℕ) (b R s0 : ℝ) :
    VectorFixedTimeParameter D (embedWidth D) 5 6 n → ℝ :=
  nativeVectorParameter (kernelCandidateFamily n D b R s0)

theorem approximation_budget_at_least_one (n D : ℕ) (hn : 0<n) (hD : 1≤D)
    (b R s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1) :
    1≤approximationWeightBudget n D b R s0 := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hD1 : (1:ℝ)≤D := by exact_mod_cast hD
  have hR1 : 1≤R := hb.trans hR
  have hs8 : s0^8≤1 := pow_le_one₀ hs0.le hs1
  unfold approximationWeightBudget
  apply (le_div_iff₀ (pow_pos hs0 8)).mpr
  have hmul : 1≤(D:ℝ)^8*(n:ℝ)^2*b^8*R^4 := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hD1) (one_le_pow₀ hn1)) (one_le_pow₀ hb))
      (one_le_pow₀ hR1)
  nlinarith only [hs8,hmul]

theorem kernel_candidate_membership {Time : Type*} (n D : ℕ) (hn : 0<n) (hD : 1≤D)
    (S : Set (KernelSpace D)) (b R s0 : ℝ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0) (hs1 : s0≤1)
    (a s : Time → ℝ) :
    (∀ j, (kernelCandidateLayout n D b R s0 j).Bounded (approximationWeightBudget n D b R s0)) ∧
    kernelCandidateParameter n D b R s0 ∈ admissibleFixedTimeParameters
      (gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
        (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation)
      (kernelCandidateLayout n D b R s0) (approximationWeightBudget n D b R s0) R := by
  have hk1 := approximation_budget_at_least_one n D hn hD b R s0 hb hR hs0 hs1
  have hclass (j : Fin D) : InScalarTransformerClass (kernelCandidateFamily n D b R s0 j) R
      (approximationWeightBudget n D b R s0) := by
    have hm := lemma_five_candidate_membership n D hD j b R s0 hb hR
    exact ⟨network_budget_mono _ _ _ hm.1
      (lemma_five_weight_budget_order n D hn hD b R s0 hb hR hs0 hs1),hm.2⟩
  exact ⟨fun j => native_layout_bounded _ _ (by linarith) (hclass j).1,
    native_gaussian_cover_membership n D hn S a s (noiseRadius D s0) _ R hk1 _ hclass⟩

theorem kernel_candidate_loss {Time : Type*} (n D : ℕ) (hn : 0<n) (S : Set (KernelSpace D))
    (b R s0 : ℝ) (a s : Time → ℝ) (p : GaussianCoverSample Time n D S) :
    fullFixedGaussianDenoisingLoss n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
      (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation
      (kernelCandidateLayout n D b R s0) (kernelCandidateParameter n D b R s0) p =
    candidateDenoisingLoss n D b R (noiseRadius D s0) s0 (a p.1) (s p.1) p.2 := by
  have hm (j : Fin D) : generalMean
      (gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s (noiseRadius D s0)
        (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation)
      (vectorFixedTimeLift (kernelCandidateLayout n D b R s0) (kernelCandidateParameter n D b R s0)) p j =
      candidateMean n D b R (noiseRadius D s0) s0 (a p.1) (s p.1) (episodeQuery n D (a p.1) (s p.1) p.2) p.2.2 j :=
    native_gaussian_mean n D hn S a s (noiseRadius D s0) (kernelCandidateFamily n D b R s0) p j
  unfold fullFixedGaussianDenoisingLoss
  dsimp only
  simp_rw [hm]
  rfl

#print axioms approximation_budget_at_least_one
#print axioms kernel_candidate_membership
#print axioms kernel_candidate_loss
end GeneralizationCheck
