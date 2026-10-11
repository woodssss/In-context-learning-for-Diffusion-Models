module

public import ICLGeneralization.ParameterGrid
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section
open scoped UniformConvergence NNReal ENNReal
namespace GeneralizationCheck

noncomputable def uniformFunctionClass {ι X : Type*} (A : Set (ι → ℝ))
    (f : (ι → ℝ) → X → ℝ) : Set (X →ᵤ ℝ) := (fun θ => UniformFun.ofFun (f θ)) '' A

noncomputable def entropyRadius (κ K M : ℝ) : ℝ := 4*κ*(K+1)+2*M

theorem finite_uniform_function_cover {ι X : Type*} [Fintype ι]
    (A : Set (ι → ℝ)) (f : (ι → ℝ) → X → ℝ) (κ K M η : ℝ)
    (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hη : 0 < η) (hηM : η ≤ M)
    (hA : ∀ θ ∈ A, ∀ i, |θ i| ≤ κ)
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ i, |θ i-θ' i| ≤ ε) →
      ∀ x, |f θ x-f θ' x| ≤ K*ε) :
    ∃ (N : ℕ) (c : Fin N → ι → ℝ), (∀ j, c j ∈ A) ∧
      (N : ℝ) ≤ (entropyRadius κ K M/η)^Fintype.card ι ∧
      ∀ θ ∈ A, ∃ j, ∀ x, |f θ x-f (c j) x| ≤ η := by
  let r := η/(2*(K+1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨N,c,hc,hN,hcover⟩ := finite_parameter_internal_cover A κ r hκ hr hA
  refine ⟨N,c,hc,?_,?_⟩
  · apply hN.trans
    apply pow_le_pow_left₀ (by positivity)
    have he : 2*κ/r+2 = (4*κ*(K+1)+2*η)/η := by dsimp [r]; field_simp; ring
    rw [he]
    exact div_le_div_of_nonneg_right (by unfold entropyRadius; linarith) hη.le
  · intro θ hθ
    obtain ⟨j,hj⟩ := hcover θ hθ
    refine ⟨j,fun x => (hLip θ hθ (c j) (hc j) (2*r) (by positivity) hj x).trans ?_⟩
    have he : (K+1)*(2*r)=η := by dsimp [r]; field_simp
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (by positivity)).trans_eq he

theorem uniform_covering_number_bound {ι X : Type*} [Fintype ι]
    (A : Set (ι → ℝ)) (f : (ι → ℝ) → X → ℝ) (N : ℕ) (c : Fin N → ι → ℝ)
    (η : ℝ≥0) (hc : ∀ j, c j ∈ A) (hcover : ∀ θ ∈ A, ∃ j, ∀ x, |f θ x-f (c j) x| ≤ η) :
    Metric.coveringNumber η (uniformFunctionClass A f) ≤ (N : ℕ∞) := by
  let C : Set (X →ᵤ ℝ) := Set.range (fun j => UniformFun.ofFun (f (c j)))
  have hC : C ⊆ uniformFunctionClass A f := by
    rintro _ ⟨j,rfl⟩
    exact ⟨c j,hc j,rfl⟩
  have hnet : Metric.IsCover η (uniformFunctionClass A f) C := by
    rintro _ ⟨θ,hθ,rfl⟩
    obtain ⟨j,hj⟩ := hcover θ hθ
    refine ⟨UniformFun.ofFun (f (c j)),⟨j,rfl⟩,?_⟩
    apply UniformFun.edist_le.mpr
    intro x
    have h := ENNReal.ofReal_le_ofReal (hj x)
    simpa only [edist_dist,Real.dist_eq,UniformFun.toFun_ofFun,ENNReal.ofReal_coe_nnreal] using h
  apply (hnet.coveringNumber_le_encard hC).trans
  have h := Set.encard_image_le (fun j => UniformFun.ofFun (f (c j))) (Set.univ : Set (Fin N))
  simpa only [Set.image_univ,Set.encard_univ,ENat.card_eq_coe_fintype_card,Fintype.card_fin] using h

theorem finite_cover_log_bound (P N : ℕ) (B η : ℝ) (hη : 0 < η) (hB : η ≤ B)
    (hN : (N : ℝ) ≤ (B/η)^P) : Real.log (N : ℝ) ≤ (P : ℝ)*Real.log (B/η) := by
  have hratio : 1 ≤ B/η := (le_div_iff₀ hη).mpr (by simpa using hB)
  by_cases hn : N=0
  · simp only [hn,Nat.cast_zero,Real.log_zero]
    exact mul_nonneg (by positivity) (Real.log_nonneg hratio)
  · have hp : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hh := Real.log_le_log hp hN
    simpa only [Real.log_pow] using hh

theorem parameterized_uniform_entropy {ι X : Type*} [Fintype ι]
    (A : Set (ι → ℝ)) (f : (ι → ℝ) → X → ℝ) (κ K M η : ℝ)
    (hκ : 0 ≤ κ) (hK : 0 ≤ K) (hη : 0 < η) (hηM : η ≤ M)
    (hA : ∀ θ ∈ A, ∀ i, |θ i| ≤ κ)
    (hLip : ∀ θ ∈ A, ∀ θ' ∈ A, ∀ ε, 0 ≤ ε → (∀ i, |θ i-θ' i| ≤ ε) →
      ∀ x, |f θ x-f θ' x| ≤ K*ε) :
    Metric.coveringNumber ⟨η,hη.le⟩ (uniformFunctionClass A f) ≠ ⊤ ∧
    Real.log ((Metric.coveringNumber ⟨η,hη.le⟩ (uniformFunctionClass A f)).toNat : ℝ) ≤
      (Fintype.card ι : ℝ)*Real.log (entropyRadius κ K M/η) := by
  obtain ⟨N,c,hc,hN,hcover⟩ := finite_uniform_function_cover A f κ K M η hκ hK hη hηM hA hLip
  have hbound := uniform_covering_number_bound A f N c ⟨η,hη.le⟩ hc hcover
  constructor
  · exact ne_top_of_le_ne_top (ENat.natCast_ne_top N) hbound
  · have hcard : ((Metric.coveringNumber ⟨η,hη.le⟩ (uniformFunctionClass A f)).toNat : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast ENat.toNat_le_of_le_natCast hbound
    have hB : η ≤ entropyRadius κ K M := by unfold entropyRadius; nlinarith
    exact finite_cover_log_bound _ _ _ _ hη hB (hcard.trans hN)

#print axioms finite_uniform_function_cover
#print axioms uniform_covering_number_bound
#print axioms finite_cover_log_bound
#print axioms parameterized_uniform_entropy
end GeneralizationCheck
