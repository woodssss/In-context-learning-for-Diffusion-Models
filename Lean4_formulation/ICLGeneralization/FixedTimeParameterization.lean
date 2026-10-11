module

public import ICLGeneralization.LemmaFourUniformTime

@[expose] public section
open MeasureTheory ProbabilityTheory
namespace GeneralizationCheck

/- The original trainable matrices are not triplicated. Schedule templates
   are fixed architectural operations, chosen before training. -/
abbrev FixedTimeParameter (D w L F m : ℕ) :=
  (Fin w × Fin D) ⊕ ((Fin L × Fin m × Fin 3 × Fin w × Fin w) ⊕
    ((Fin L × Fin F × ((Fin w × Fin w) ⊕ Fin w)) ⊕ Fin w))
abbrev VectorFixedTimeParameter (D w L F m : ℕ) := Fin D × FixedTimeParameter D w L F m

structure FixedTimeLayout (w L m : ℕ) where
  alpha : Fin L → Fin m → Fin 3 → Fin w → Fin w → ℝ
  reciprocal : Fin L → Fin m → Fin 3 → Fin w → Fin w → ℝ

noncomputable def fixedTimeParameterCount (D w L F m : ℕ) : ℕ :=
  w*(D+1)+L*(3*m*w^2+F*(w^2+w))

def FixedTimeLayout.Bounded {w L m : ℕ} (A : FixedTimeLayout w L m) (κ : ℝ) : Prop :=
  (∀ k i h r c, |A.alpha k i h r c| ≤ κ) ∧ ∀ k i h r c, |A.reciprocal k i h r c| ≤ κ

noncomputable def fixedTimeLift {D w L F m : ℕ} (A : FixedTimeLayout w L m)
    (θ : FixedTimeParameter D w L F m → ℝ) : GeneralParameter D w L F m → ℝ
  | .inl p => θ (.inl p)
  | .inr (.inl (k,i,h,j,r,c)) => if j=0 then θ (.inr (.inl (k,i,h,r,c)))
      else if j=1 then A.alpha k i h r c else A.reciprocal k i h r c
  | .inr (.inr p) => θ (.inr (.inr p))

noncomputable def vectorFixedTimeLift {D w L F m : ℕ} (A : Fin D → FixedTimeLayout w L m)
    (θ : VectorFixedTimeParameter D w L F m → ℝ) : VectorGeneralParameter D w L F m → ℝ :=
  fun p => fixedTimeLift (A p.1) (fun j => θ (p.1,j)) p.2

theorem fixed_time_parameter_count (D w L F m : ℕ) :
    Fintype.card (FixedTimeParameter D w L F m) = fixedTimeParameterCount D w L F m := by
  simp only [FixedTimeParameter,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,fixedTimeParameterCount]
  ring

theorem vector_fixed_time_parameter_count (D w L F m : ℕ) :
    Fintype.card (VectorFixedTimeParameter D w L F m) = D*fixedTimeParameterCount D w L F m := by
  simp only [VectorFixedTimeParameter,Fintype.card_prod,Fintype.card_fin,fixed_time_parameter_count]

theorem fixed_time_parameter_count_le_two_paper (D w L F m : ℕ) :
    fixedTimeParameterCount D w L F m ≤ 2*paperParameterCount D w L F m := by
  have hw : w ≤ w^2 := by
    by_cases h : w=0
    · simp [h]
    · have : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr h
      nlinarith
  have hh : 3*m*w^2+F*(w^2+w) ≤ 2*(3*w^2*m+F*w^2) := by
    have h := Nat.mul_le_mul_left F hw
    nlinarith
  have he : w*(D+1) ≤ 2*(w*(D+1)) := by omega
  exact (Nat.add_le_add he (Nat.mul_le_mul_left L hh)).trans_eq (by unfold paperParameterCount; ring)

theorem fixed_time_lift_bounded {D w L F m : ℕ} (A : FixedTimeLayout w L m)
    (θ : FixedTimeParameter D w L F m → ℝ) (κ : ℝ)
    (hA : A.Bounded κ) (hθ : ∀ p, |θ p| ≤ κ) : ∀ p, |fixedTimeLift A θ p| ≤ κ := by
  intro p
  rcases p with p|p
  · exact hθ _
  · rcases p with ⟨k,i,h,j,r,c⟩|p
    · simp only [fixedTimeLift]
      split_ifs
      · exact hθ _
      · exact hA.1 k i h r c
      · exact hA.2 k i h r c
    · exact hθ _

theorem fixed_time_lift_perturbation {D w L F m : ℕ} (A : FixedTimeLayout w L m)
    (θ θ' : FixedTimeParameter D w L F m → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (he : ∀ p, |θ p-θ' p| ≤ ε) : ∀ p, |fixedTimeLift A θ p-fixedTimeLift A θ' p| ≤ ε := by
  intro p
  rcases p with p|p
  · exact he _
  · rcases p with ⟨k,i,h,j,r,c⟩|p
    · simp only [fixedTimeLift]
      split_ifs
      · exact he _
      · simpa only [sub_self,abs_zero] using hε
      · simpa only [sub_self,abs_zero] using hε
    · exact he _

theorem fixed_time_matrix_eval {D w L F m : ℕ} (A : FixedTimeLayout w L m)
    (θ : FixedTimeParameter D w L F m → ℝ) (k : Fin L) (i : Fin m) (h : Fin 3) (a s : ℝ) (r c : Fin w) :
    (generalScheduledMatrix (fixedTimeLift A θ) k i h).eval a s r c =
      θ (.inr (.inl (k,i,h,r,c)))+a*A.alpha k i h r c+(1/s)*A.reciprocal k i h r c := by
  simp [generalScheduledMatrix,ScheduledMatrix.eval,fixedTimeLift]

#print axioms fixed_time_parameter_count
#print axioms vector_fixed_time_parameter_count
#print axioms fixed_time_parameter_count_le_two_paper
#print axioms fixed_time_lift_bounded
#print axioms fixed_time_lift_perturbation
#print axioms fixed_time_matrix_eval
end GeneralizationCheck
