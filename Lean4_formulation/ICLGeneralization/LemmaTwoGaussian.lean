module

public import ICLGeneralization.RestrictionTransfer

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem lemma_two_gaussian_original {Time Θ : Type*} [MeasurableSpace Time] [MeasurableSpace Θ]
    (n D w L F m K J N : ℕ) (hn : 0<n) (hD : 0<D) (hw : 0<w) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (S : Set (KernelSpace D)) (a s : Time → ℝ) (ham : Measurable a) (hsm : Measurable s)
    (PE tokenMask : Fin (n+1) → Fin w → ℝ) (hp : ∀ q r, |PE q r|≤1) (ht : ∀ q r, |tokenMask q r|≤1)
    (softmax : Fin L → Bool) (activation : Fin L → Fin F → Bool)
    (layout : Fin D → FixedTimeLayout w L m) (κ R b s0 : ℝ)
    (hLayout : ∀ j, (layout j).Bounded κ) (hκ : 0≤κ) (hb : 1≤b) (hR : b≤R) (hs0 : 0<s0)
    (ha : ∀ t, 0≤a t ∧ a t≤1) (hs : ∀ t, s0≤s t ∧ s t≤1)
    (hbox : ∀ x ∈ S, ∀ j, x j ∈ Set.Icc (-b) b)
    (μTime : Measure Time) [IsProbabilityMeasure μTime]
    (μTask : Measure Θ) [IsProbabilityMeasure μTask] (ρ : Kernel Θ S) [IsMarkovKernel ρ]
    (learn : HierarchicalTrainingSample Θ (CleanPromptSample n D S) (GaussianCoverSample Time n D S) K J N →
      admissibleFixedTimeParameters (gaussianLossSetup n D w L F m (S:=S) a s (noiseRadius D s0)
        PE tokenMask softmax activation) layout κ R) (hl : Measurable learn) :
    let f := fun θ => fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s (noiseRadius D s0)
      PE tokenMask softmax activation layout θ.val
    let B := verifiedLossCoverConstant D w m (n+1) F L κ R b s0 (max 1 (b+noiseRadius D s0))
    let M := lossEnvelope D R b s0
    (∫ z, adaptiveHierarchyGap K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime) f learn z
      ∂hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)) ≤
    4*M*hierarchicalSamplingFactor K J N*
      (6*Real.sqrt ((D*fixedTimeParameterCount D w L F m:ℝ)*Real.log (B*Real.sqrt ((K*J)*N:ℝ)/M))+1)+
      M*(gaussianNoiseLaw D {eps | noiseRadius D s0<‖eps‖}).toReal := by
  dsimp only
  let model := gaussianLossSetup n D w L F m (S:=S) a s (noiseRadius D s0) PE tokenMask softmax activation
  let A := admissibleFixedTimeParameters model layout κ R
  let U := max 1 (b+noiseRadius D s0)
  let M := lossEnvelope D R b s0
  let C := lossSensitivity D w m (n+1) F L κ R b s0 U
  let fc := restrictedFixedTimeLoss model layout
  let f := fullFixedTimeLoss model layout
  have hb0 : 0≤b := by linarith
  have hR0 : 0≤R := by linarith
  have hU : 0≤U := (by dsimp [U]; exact (le_trans (by norm_num) (le_max_left _ _)))
  have hM : 0<M := by unfold M lossEnvelope; positivity
  have hC : 0≤C := loss_sensitivity_nonnegative D w m (n+1) F L κ R b s0 U hκ hR0 hb0 hs0 hU
  have hxm := measurable_gaussian_raw_input n D S a s ham hsm
  have hzm (j : Fin D) : Measurable (fun p : GaussianCoverSample Time n D S => model.clean p j) :=
    (measurable_clean_coordinate j).comp measurable_snd.fst.fst
  have hz (p : GaussianCoverSample Time n D S) (j : Fin D) : |model.clean p j|≤b := abs_le.mpr (hbox _ p.2.1.1.property j)
  have ha' (p : GaussianCoverSample Time n D S) : 0≤model.alpha p ∧ model.alpha p≤1 := ha p.1
  have hs' (p : GaussianCoverSample Time n D S) : s0≤model.sigma p := (hs p.1).1
  have hfm (θ) (_hθ : θ∈A) : Measurable (f θ) := full_fixed_loss_measurable model layout θ hxm
    (ham.comp measurable_fst) (hsm.comp measurable_fst) hzm
  have hfc (θ) (_hθ : θ∈A) : Measurable (fc θ) := measurable_restricted_general_loss model (vectorFixedTimeLift layout θ)
    hxm (ham.comp measurable_fst) (hsm.comp measurable_fst) hzm (measurableSet_le (by fun_prop) measurable_const)
  have hfB (θ) (hθ : θ∈A) : ∀ p, |f θ p|≤M := full_fixed_loss_envelope model layout θ κ R b s0 hθ hR0 hb0 hs0 ha' hs' hz
  have hcB (θ) (hθ : θ∈A) : ∀ p, |fc θ p|≤M := restricted_general_loss_envelope model (vectorFixedTimeLift layout θ)
    κ R b s0 (fixed_time_admissible_lift model layout κ R hLayout θ hθ) hR0 hb0 hs0 ha' hs' hz
  have hx (p : GaussianCoverSample Time n D S) (he : p∈model.event) : ∀ q r, |model.input p q r|≤U :=
    gaussian_raw_input_bound n D S a s b (noiseRadius D s0) hb0 (noise_radius_nonnegative D s0) ha
      (fun t => ⟨(lt_of_lt_of_le hs0 (hs t).1).le,(hs t).2⟩) hbox p he
  have hLip : ∀ θ∈A, ∀ θ'∈A, ∀ ε, 0≤ε → (∀ p, |θ p-θ' p|≤ε) → ∀ p, |fc θ p-fc θ' p|≤C*ε := by
    intro θ hθ θ' hθ' ε hε he
    exact restricted_general_loss_perturbation hn model (vectorFixedTimeLift layout θ) (vectorFixedTimeLift layout θ')
      κ R b s0 U ε hκ hR0 hb0 hs0 hU hε
      (fixed_time_admissible_lift model layout κ R hLayout θ hθ) (fixed_time_admissible_lift model layout κ R hLayout θ' hθ')
      (fun p => fixed_time_lift_perturbation (layout p.1) _ _ ε hε (fun q => he (p.1,q)) p.2)
      hp ht ha' hs' hz hx
  let : Nonempty (VectorFixedTimeParameter D w L F m) := ⟨(⟨0,hD⟩,Sum.inl (⟨0,hw⟩,⟨0,hD⟩))⟩
  let law := hierarchicalTrainingLaw K J N μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
  let : Nonempty (HierarchicalTrainingSample Θ (CleanPromptSample n D S) (GaussianCoverSample Time n D S) K J N) :=
    nonempty_of_isProbabilityMeasure law
  have hAne : A.Nonempty := ⟨(learn (Classical.arbitrary _)).val,(learn (Classical.arbitrary _)).property⟩
  have hcJoin := parameterized_loss_joint_measurable A fc (fun _ => C) (fun _ => hC) hfc hLip
  have hfJoin := full_fixed_loss_joint_measurable hn model layout κ R b s0 hLayout hκ hR0 hb0 hs0 hp ht ha' hs' hz
    hxm (ham.comp measurable_fst) (hsm.comp measurable_fst) hzm
  have hpop (θ : A) : hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime) (f θ.val)-
      hierarchicalPopulationLoss μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime) (fc θ.val) ≤
      M*(gaussianNoiseLaw D {eps | noiseRadius D s0<‖eps‖}).toReal :=
    hierarchy_population_upper_gap μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
      _ _ (hfm θ.val θ.property) (hfc θ.val θ.property) M _ (hfB θ.val θ.property) (hcB θ.val θ.property)
      (gaussian_restriction_episode_tail n D w L F m S a s (noiseRadius D s0) M hM.le PE tokenMask softmax activation layout θ.val μTime
        (hfm θ.val θ.property) (hfc θ.val θ.property) (hfB θ.val θ.property))
  have htr := adaptive_restriction_transfer K J N hK hJ hN μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
    (fun θ : A => f θ.val) (fun θ : A => fc θ.val) hfJoin hcJoin M _
    (fun θ => hfB θ.val θ.property) (fun θ => hcB θ.val θ.property)
    (fun θ => restricted_fixed_loss_le_full model layout θ.val) hpop learn hl
  have hstat := lemma_two_parameterized K J N hK hJ hN μTask (cleanPromptKernel n D ρ) (timeNoiseEpisodeKernel n D S μTime)
    A hAne fc κ C M hκ hC hM (fun θ hθ => hθ.1) hfc hcB hLip learn hl
  have he : (fun θ : A => fullFixedGaussianDenoisingLoss n D w L F m (S:=S) a s (noiseRadius D s0)
      PE tokenMask softmax activation layout θ.val) = (fun θ : A => f θ.val) := by
    funext θ p
    exact full_gaussian_loss_is_DSM n D w L F m a s (noiseRadius D s0) PE tokenMask softmax activation layout θ.val p
      (ne_of_gt (lt_of_lt_of_le hs0 (hs p.1).1))
  rw [he]
  simpa only [vector_fixed_time_parameter_count,M,C,U,verifiedLossCoverConstant,Nat.cast_mul] using
    htr.trans (add_le_add hstat (le_refl _))

#print axioms lemma_two_gaussian_original
end GeneralizationCheck
