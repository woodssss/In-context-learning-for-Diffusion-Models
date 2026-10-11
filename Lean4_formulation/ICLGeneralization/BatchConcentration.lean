module

public import ICLGeneralization.IndependentBatch

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GeneralizationCheck

theorem independent_average_subgaussian {Y : Type*} [MeasurableSpace Y]
    (N : ℕ) (hN : 0<N) (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
    (f : Y → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ y, |f y|≤M) :
    HasSubgaussianMGF (sampleDeviation N μ f) ⟨M^2/(N:ℝ),by positivity⟩ (Measure.pi μ) := by
  have hn : 0<(N:ℝ) := by exact_mod_cast hN
  let c : ℝ≥0 := ⟨M^2,sq_nonneg M⟩
  have hc (i : Fin N) : HasSubgaussianMGF (fun y => f y-∫ z, f z ∂μ i) c (μ i) := by
    have h := hasSubgaussianMGF_of_mem_Icc hf.aemeasurable
      (ae_of_all (μ i) (fun y => abs_le.mp (hb y)))
    convert h using 1
    apply NNReal.eq
    change M^2 = ((|M-(-M)|)/2)^2
    rw [sub_neg_eq_add,←two_mul,abs_mul,abs_of_nonneg hM]
    norm_num
  have hev (i : Fin N) : HasSubgaussianMGF (fun x : Fin N → Y => f (x i)-∫ z, f z ∂μ i) c (Measure.pi μ) := by
    have hmap := (measurePreserving_eval μ i).map_eq
    have h : HasSubgaussianMGF (fun y => f y-∫ z, f z ∂μ i) c
        (Measure.map (Function.eval i) (Measure.pi μ)) := by rw [hmap]; exact hc i
    exact HasSubgaussianMGF.of_map (Y:=Function.eval i) (μ:=Measure.pi μ)
      (X:=fun y => f y-∫ z, f z ∂μ i) (measurable_pi_apply i).aemeasurable h
  have hind := iIndepFun_pi (μ:=μ) (X:=fun i y => f y-∫ z, f z ∂μ i)
    (fun i => (hf.sub_const _).aemeasurable)
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hind (s:=Finset.univ) (fun i _ => hev i)
  have hav := (hsum.const_mul (1/(N:ℝ))).neg
  have he : (fun x : Fin N → Y => -((1/(N:ℝ))*(∑ i, (f (x i)-∫ z, f z ∂μ i)))) =
      sampleDeviation N μ f := by
    funext x
    unfold sampleDeviation populationAverage sampleAverage
    rw [Finset.sum_sub_distrib]
    ring
  have hp : (⟨(1/(N:ℝ))^2,sq_nonneg _⟩*(∑ _i : Fin N,c) : ℝ≥0) = ⟨M^2/(N:ℝ),by positivity⟩ := by
    apply Subtype.ext
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (1/(N:ℝ))^2*((N:ℝ)*M^2) = M^2/(N:ℝ)
    field_simp
  rw [hp] at hav
  exact hav.congr (ae_of_all _ (fun x => congrFun he x))

theorem independent_average_hoeffding {Y : Type*} [MeasurableSpace Y]
    (N : ℕ) (hN : 0<N) (μ : Fin N → Measure Y) [∀ i, IsProbabilityMeasure (μ i)]
    (f : Y → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ y, |f y|≤M)
    (u : ℝ) (hu : 0≤u) :
    (Measure.pi μ).real {x | u≤sampleDeviation N μ f x} ≤
      Real.exp (-u^2/(2*(M^2/(N:ℝ)))) :=
  (independent_average_subgaussian N hN μ f hf M hM hb).measure_ge_le hu

#print axioms independent_average_subgaussian
#print axioms independent_average_hoeffding
end GeneralizationCheck
