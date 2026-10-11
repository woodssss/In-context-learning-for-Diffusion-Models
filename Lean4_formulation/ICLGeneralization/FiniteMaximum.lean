module

public import ICLGeneralization.BatchConcentration
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GeneralizationCheck

noncomputable def finiteMaximum {I Ω : Type*} [Fintype I] [Nonempty I] (Z : I → Ω → ℝ) : Ω → ℝ :=
  fun ω => Finset.univ.sup' Finset.univ_nonempty (fun i => Z i ω)

theorem finite_maximum_measurable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i)) : Measurable (finiteMaximum Z) := by
  classical
  have h := Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hZ i)
  have he : finiteMaximum Z = Finset.univ.sup' Finset.univ_nonempty Z := by
    funext ω
    exact (Finset.sup'_apply _ Z ω).symm
  rw [he]
  exact h

theorem finite_maximum_le {I Ω : Type*} [Fintype I] [Nonempty I]
    (Z : I → Ω → ℝ) (i : I) (ω : Ω) : Z i ω≤finiteMaximum Z ω := by
  classical
  exact Finset.le_sup' (fun j => Z j ω) (Finset.mem_univ i)

theorem finite_maximum_abs_bound {I Ω : Type*} [Fintype I] [Nonempty I]
    (Z : I → Ω → ℝ) (B : ℝ) (hb : ∀ i ω, |Z i ω|≤B) : ∀ ω, |finiteMaximum Z ω|≤B := by
  classical
  intro ω
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp (hb (Classical.arbitrary I) ω)).1.trans (finite_maximum_le Z _ ω)
  · exact Finset.sup'_le _ _ (fun i _ => (abs_le.mp (hb i ω)).2)

theorem finite_maximum_exponential_bound {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (B c t : ℝ) (hb : ∀ i ω, |Z i ω|≤B) (_ht : 0<t)
    (hm : ∀ i, (∫ ω, Real.exp (t*Z i ω) ∂μ)≤Real.exp (c*t^2/2)) :
    t*(∫ ω, finiteMaximum Z ω ∂μ) ≤ Real.log (Fintype.card I:ℝ)+c*t^2/2 := by
  classical
  have hmeas := finite_maximum_measurable Z hZ
  have hbound := finite_maximum_abs_bound Z B hb
  have hi := (bounded_probability_integral μ _ hmeas B hbound).1
  have hexpb : ∀ ω, |Real.exp (t*finiteMaximum Z ω)|≤Real.exp (|t| * B) := by
    intro ω
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hbound ω) (abs_nonneg t))
  have hexpm : Measurable (fun ω => Real.exp (t*finiteMaximum Z ω)) :=
    Real.continuous_exp.measurable.comp (hmeas.const_mul t)
  have hexpi := (bounded_probability_integral μ _ hexpm _ hexpb).1
  have heach (i : I) : Integrable (fun ω => Real.exp (t*Z i ω)) μ := by
    apply (bounded_probability_integral μ _ (Real.continuous_exp.measurable.comp ((hZ i).const_mul t))
      (Real.exp (|t| * B)) ?_).1
    intro ω
    change |Real.exp (t*Z i ω)|≤_
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i ω) (abs_nonneg t))
  have hsumi := integrable_finsetSum Finset.univ (fun i _ => heach i)
  have hpoint (ω : Ω) : Real.exp (t*finiteMaximum Z ω)≤∑ i, Real.exp (t*Z i ω) := by
    obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => Z i ω)
    unfold finiteMaximum
    rw [he]
    exact Finset.single_le_sum (f:=fun j => Real.exp (t*Z j ω)) (fun j _ => (Real.exp_pos _).le) hi
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all μ (fun ω => Set.mem_univ (t*finiteMaximum Z ω))) (hi.const_mul t) hexpi
  rw [integral_const_mul] at hj
  have hs : (∫ ω, Real.exp (t*finiteMaximum Z ω) ∂μ)≤(Fintype.card I:ℝ)*Real.exp (c*t^2/2) := by
    apply (integral_mono hexpi hsumi hpoint).trans
    rw [integral_finsetSum _ (fun i _ => heach i)]
    exact (Finset.sum_le_sum (fun i _ => hm i)).trans_eq (by simp)
  have hn : 0<(Fintype.card I:ℝ) := by exact_mod_cast Fintype.card_pos
  have hl := Real.log_le_log (Real.exp_pos _) (hj.trans hs)
  rw [Real.log_exp,Real.log_mul (ne_of_gt hn) (ne_of_gt (Real.exp_pos _)),Real.log_exp] at hl
  exact hl

#print axioms finite_maximum_measurable
#print axioms finite_maximum_le
#print axioms finite_maximum_abs_bound
#print axioms finite_maximum_exponential_bound
end GeneralizationCheck
