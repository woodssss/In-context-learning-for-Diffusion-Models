module

public import ICLGeneralization.LemmaTwoParameterized
public import ICLGeneralization.GaussianLossTail

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

theorem probability_integral_upper_gap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M C : ℝ) (hb : ∀ ω, |f ω|≤M) (hb' : ∀ ω, |g ω|≤M) (he : ∀ ω, f ω-g ω≤C) :
    (∫ ω, f ω ∂μ)-(∫ ω, g ω ∂μ)≤C := by
  have fi := (bounded_probability_integral μ f hf M hb).1
  have gi := (bounded_probability_integral μ g hg M hb').1
  have di : Integrable (fun ω => f ω-g ω) μ := fi.sub gi
  have h := integral_mono di (integrable_const C) he
  rw [integral_sub fi gi] at h
  simpa using h

theorem hierarchy_population_upper_gap {Θ X Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) (M C : ℝ)
    (hb : ∀ ω, |f ω|≤M) (hb' : ∀ ω, |g ω|≤M)
    (he : ∀ x, (∫ ω, f ω ∂κEpisode x)-(∫ ω, g ω ∂κEpisode x)≤C) :
    hierarchicalPopulationLoss μ κTask κEpisode f-hierarchicalPopulationLoss μ κTask κEpisode g≤C := by
  let h := fun x => ∫ ω, f ω ∂κEpisode x
  let h' := fun x => ∫ ω, g ω ∂κEpisode x
  have hm : Measurable h := kernel_average_measurable (fun (_ : Unit → ℝ) => f) κEpisode (fun _ => 0) hf
  have hm' : Measurable h' := kernel_average_measurable (fun (_ : Unit → ℝ) => g) κEpisode (fun _ => 0) hg
  have hB (x : X) : |h x|≤M := (bounded_probability_integral (κEpisode x) f hf M hb).2
  have hB' (x : X) : |h' x|≤M := (bounded_probability_integral (κEpisode x) g hg M hb').2
  let k := fun t => ∫ x, h x ∂κTask t
  let k' := fun t => ∫ x, h' x ∂κTask t
  have km : Measurable k := kernel_average_measurable (fun (_ : Unit → ℝ) => h) κTask (fun _ => 0) hm
  have km' : Measurable k' := kernel_average_measurable (fun (_ : Unit → ℝ) => h') κTask (fun _ => 0) hm'
  have kB (t : Θ) : |k t|≤M := (bounded_probability_integral (κTask t) h hm M hB).2
  have kB' (t : Θ) : |k' t|≤M := (bounded_probability_integral (κTask t) h' hm' M hB').2
  have ke (t : Θ) : k t-k' t≤C := probability_integral_upper_gap (κTask t) h h' hm hm' M C hB hB' he
  exact probability_integral_upper_gap μ k k' km km' M C kB kB' ke

theorem hierarchy_empirical_mono {Θ X Ω : Type*} (K J N : ℕ) (f g : Ω → ℝ)
    (he : ∀ ω, g ω≤f ω) (s : HierarchicalTrainingSample Θ X Ω K J N) :
    hierarchicalEmpiricalLoss K J N g s≤hierarchicalEmpiricalLoss K J N f s := by
  unfold hierarchicalEmpiricalLoss sampleAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => he _)) (by positivity)

theorem adaptive_restriction_transfer {P Θ X Ω : Type*}
    [MeasurableSpace P] [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Ω]
    (K J N : ℕ) (hK : 0<K) (hJ : 0<J) (hN : 0<N)
    (μ : Measure Θ) [IsProbabilityMeasure μ] (κTask : Kernel Θ X) [IsMarkovKernel κTask]
    (κEpisode : Kernel X Ω) [IsMarkovKernel κEpisode]
    (f g : P → Ω → ℝ) (hf : Measurable (fun p : P × Ω => f p.1 p.2))
    (hg : Measurable (fun p : P × Ω => g p.1 p.2)) (M C : ℝ)
    (hb : ∀ θ ω, |f θ ω|≤M) (hb' : ∀ θ ω, |g θ ω|≤M)
    (he : ∀ θ ω, g θ ω≤f θ ω)
    (hpop : ∀ θ, hierarchicalPopulationLoss μ κTask κEpisode (f θ)-hierarchicalPopulationLoss μ κTask κEpisode (g θ)≤C)
    (learn : HierarchicalTrainingSample Θ X Ω K J N → P) (hl : Measurable learn) :
    (∫ z, adaptiveHierarchyGap K J N μ κTask κEpisode f learn z ∂hierarchicalTrainingLaw K J N μ κTask κEpisode) ≤
      (∫ z, adaptiveHierarchyGap K J N μ κTask κEpisode g learn z ∂hierarchicalTrainingLaw K J N μ κTask κEpisode)+C := by
  have hi := adaptive_gap_integrable K J N hK hJ hN μ κTask κEpisode f hf learn hl M hb
  have gi := adaptive_gap_integrable K J N hK hJ hN μ κTask κEpisode g hg learn hl M hb'
  have sumI : Integrable (fun z => adaptiveHierarchyGap K J N μ κTask κEpisode g learn z+C)
      (hierarchicalTrainingLaw K J N μ κTask κEpisode) := gi.add (integrable_const C)
  have hpoint (z) : adaptiveHierarchyGap K J N μ κTask κEpisode f learn z≤
      adaptiveHierarchyGap K J N μ κTask κEpisode g learn z+C := by
    have ha := hierarchy_empirical_mono K J N (f (learn z)) (g (learn z)) (he (learn z)) z
    have hp := hpop (learn z)
    unfold adaptiveHierarchyGap
    linarith
  have h := integral_mono hi sumI hpoint
  rw [integral_add gi (integrable_const C)] at h
  simpa using h

#print axioms probability_integral_upper_gap
#print axioms hierarchy_population_upper_gap
#print axioms hierarchy_empirical_mono
#print axioms adaptive_restriction_transfer
end GeneralizationCheck
