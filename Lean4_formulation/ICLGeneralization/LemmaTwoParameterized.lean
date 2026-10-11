module

public import ICLGeneralization.AdaptiveGridBound

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

/- The stated statistical-error bound follows directly from the original
   coefficient grid and independent bounded sampling. No entropy integral
   or statistical-error conclusion is supplied as an input. -/
theorem lemma_two_parameterized {ι Θ X Ω : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (A : Set (ι → ℝ)) (hAne : A.Nonempty) (f : (ι → ℝ) → Ω → ℝ)
    (κ C M : ℝ) (hκ : 0≤κ) (hC : 0≤C) (hM : 0<M)
    (hA : ∀ θ ∈ A, ∀ p, |θ p|≤κ) (hf : ∀ θ ∈ A, Measurable (f θ))
    (hb : ∀ θ ∈ A, ∀ ω, |f θ ω|≤M)
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0≤ε → (∀ p, |θ p-θ' p|≤ε) → ∀ ω, |f θ ω-f θ' ω|≤C*ε)
    (learn : HierarchicalTrainingSample Θ X Ω K J N → A) (hl : Measurable learn) :
    (∫ z, adaptiveHierarchyGap K J N μ κTask κEpisode (fun θ : A => f θ.val) learn z
      ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
      4*M*hierarchicalSamplingFactor K J N*
        (6*Real.sqrt ((Fintype.card ι:ℝ)*Real.log (entropyRadius κ C M*Real.sqrt ((K*J)*N:ℝ)/M))+1) := by
  have hTot : 0<(K*J)*N := Nat.mul_pos (Nat.mul_pos hK hJ) hN
  have hTotR : 0<((K*J)*N:ℝ) := by positivity
  have hTot1 : 1≤((K*J)*N:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_of_gt hTot)
  have hsqrt : 0<Real.sqrt ((K*J)*N:ℝ) := Real.sqrt_pos.mpr hTotR
  have hsqrt1 : 1≤Real.sqrt ((K*J)*N:ℝ) := by nlinarith [Real.sq_sqrt hTotR.le,Real.sqrt_nonneg ((K*J)*N:ℝ)]
  let η := M/Real.sqrt ((K*J)*N:ℝ)
  let B := entropyRadius κ C M
  let H := (Fintype.card ι:ℝ)*Real.log (B/η)
  have hη : 0<η := by dsimp [η]; positivity
  have hηM : η≤M := by dsimp [η]; exact (div_le_self hM.le hsqrt1)
  have hBM : 2*M≤B := by dsimp [B,entropyRadius]; nlinarith
  have hratio : 1<B/η := (lt_div_iff₀ hη).mpr (by linarith)
  have hH : 0<H := mul_pos (by exact_mod_cast Fintype.card_pos) (Real.log_pos hratio)
  obtain ⟨Nc,c,hc,hcount,hcover⟩ := finite_uniform_function_cover A f κ C M η hκ hC hη hηM hA hLip
  obtain ⟨θ0,hθ0⟩ := hAne
  obtain ⟨j0,_⟩ := hcover θ0 hθ0
  let : Nonempty (Fin Nc) := ⟨j0⟩
  have hjoin := parameterized_loss_joint_measurable A f (fun _ => C) (fun _ => hC) hf hLip
  have hgrid := adaptive_grid_bound K J N hK hJ hN μ κTask κEpisode (fun θ : A => f θ.val)
    hjoin learn hl (fun i => (⟨c i,hc i⟩:A)) M H η hM hH (fun θ => hb θ.val θ.property)
    (fun θ => hcover θ.val θ.property) (by
      simpa only [Fintype.card_fin] using finite_cover_log_bound (Fintype.card ι) Nc B η hη (by linarith) hcount)
  have he : B/η=B*Real.sqrt ((K*J)*N:ℝ)/M := by dsimp [η]; field_simp
  have hFac : 0≤hierarchicalSamplingFactor K J N := by unfold hierarchicalSamplingFactor; positivity
  have hηFac : η≤M*hierarchicalSamplingFactor K J N := by
    have hr : 1/Real.sqrt ((K*J)*N:ℝ)≤hierarchicalSamplingFactor K J N := by
      unfold hierarchicalSamplingFactor
      have h1 : 0≤1/Real.sqrt (K:ℝ) := by positivity
      have h2 : 0≤1/Real.sqrt (K*J:ℝ) := by positivity
      linarith
    have hh := mul_le_mul_of_nonneg_left hr hM.le
    simpa only [η,mul_one_div] using hh
  apply hgrid.trans
  change 2*M*Real.sqrt H*hierarchicalSamplingFactor K J N+2*η≤_
  have hHid : H=(Fintype.card ι:ℝ)*Real.log (B*Real.sqrt ((K*J)*N:ℝ)/M) := by dsimp [H]; rw [he]
  rw [←hHid]
  have hp : 0≤M*hierarchicalSamplingFactor K J N*Real.sqrt H := by positivity
  nlinarith

#print axioms lemma_two_parameterized
end GeneralizationCheck
