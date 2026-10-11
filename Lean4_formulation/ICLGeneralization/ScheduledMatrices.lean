module

public import ICLGeneralization.MatrixBlocks

@[expose] public section

open Matrix
namespace GeneralizationCheck

/- Each record contains only fixed matrices. The two prescribed time operations
   multiply these matrices by alpha and reciprocal sigma during evaluation. -/
structure ScheduledMatrix (d : ℕ) where
  base : Matrix (Fin d) (Fin d) ℝ
  alpha : Matrix (Fin d) (Fin d) ℝ
  reciprocal : Matrix (Fin d) (Fin d) ℝ

noncomputable def ScheduledMatrix.eval {d : ℕ} (A : ScheduledMatrix d) (a s : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun r c => A.base r c+a*A.alpha r c+(1/s)*A.reciprocal r c

noncomputable def fixedMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ScheduledMatrix d :=
  ⟨A,0,0⟩
noncomputable def alphaMatrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : ScheduledMatrix d :=
  ⟨0,A,0⟩

theorem fixed_matrix_eval {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ) :
    (fixedMatrix A).eval a s = A := by
  funext r c
  simp [fixedMatrix, ScheduledMatrix.eval]

theorem alpha_matrix_eval {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (a s : ℝ) :
    (alphaMatrix A).eval a s = fun r c => a*A r c := by
  funext r c
  simp [alphaMatrix, ScheduledMatrix.eval]

noncomputable def liftData (D : ℕ)
    (A : Matrix (Fin (coreWidth D)) (Fin (embedWidth D)) ℝ) :
    Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ :=
  fun r c => Fin.addCases (fun p => A p c) (fun _ : Fin 3 => 0) r

noncomputable def scheduledDistanceQuery (n D : ℕ) (M : ℝ) (i : Fin (n+1)) :
    ScheduledMatrix (embedWidth D) where
  base := extendedQuery (coreWidth D) (n+1) (4*M*(n+1 : ℝ)^2) i (distanceData D M 1 0)
  alpha := 0
  reciprocal := liftData D (distanceData D 0 1 1)

noncomputable def scheduledDistanceKey (n D : ℕ) (M : ℝ) (i : Fin (n+1)) :
    ScheduledMatrix (embedWidth D) where
  base := extendedKey (coreWidth D) (n+1) (4*M*(n+1 : ℝ)^2) i (distanceData D M 1 0)
  alpha := 0
  reciprocal := liftData D (distanceData D 0 1 (-1))

theorem distance_data_schedule (D : ℕ) (M s sign : ℝ) (r : Fin (coreWidth D))
    (c : Fin (embedWidth D)) :
    distanceData D M s sign r c = distanceData D M 1 0 r c+
      (1/s)*distanceData D 0 1 sign r c := by
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simp [distanceData]
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · simp only [distanceData, Fin.addCases_left, Fin.addCases_right, zero_div, zero_mul, zero_add,
        mul_one]
      ring
    · fin_cases r <;> simp [distanceData]

theorem scheduled_distance_query_eval (n D : ℕ) (M a s : ℝ) (i : Fin (n+1)) :
    (scheduledDistanceQuery n D M i).eval a s =
    extendedQuery (coreWidth D) (n+1) (2*(2*M)*(n+1 : ℝ)^2) i (distanceData D M s 1) := by
  funext r c
  have hC : 4*M*(n+1 : ℝ)^2=2*(2*M)*(n+1 : ℝ)^2 := by ring
  simp only [ScheduledMatrix.eval, scheduledDistanceQuery, Matrix.zero_apply, mul_zero, add_zero, hC]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simp only [extendedQuery, liftData, Fin.addCases_left]
    exact (distance_data_schedule D M s 1 r c).symm
  · simp [extendedQuery, liftData]

theorem scheduled_distance_key_eval (n D : ℕ) (M a s : ℝ) (i : Fin (n+1)) :
    (scheduledDistanceKey n D M i).eval a s =
    extendedKey (coreWidth D) (n+1) (2*(2*M)*(n+1 : ℝ)^2) i (distanceData D M s (-1)) := by
  funext r c
  have hC : 4*M*(n+1 : ℝ)^2=2*(2*M)*(n+1 : ℝ)^2 := by ring
  simp only [ScheduledMatrix.eval, scheduledDistanceKey, Matrix.zero_apply, mul_zero, add_zero, hC]
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · simp only [extendedKey, liftData, Fin.addCases_left]
    exact (distance_data_schedule D M s (-1) r c).symm
  · simp [extendedKey, liftData]

theorem difference_value_alpha_eval (D : ℕ) (a s : ℝ) :
    (alphaMatrix (differenceValueMatrix D (-1))).eval a s = differenceValueMatrix D (-a) := by
  rw [alpha_matrix_eval]
  funext r c
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r <;>
        simp [differenceValueMatrix, writeRows]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [differenceValueMatrix, writeRows]
      · fin_cases r <;> simp [differenceValueMatrix, writeRows]
  · simp [differenceValueMatrix, writeRows]

noncomputable def rankOneRead {d : ℕ} (out source : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun r c => readRow out r*readRow source c

theorem rank_one_read_action {d : ℕ} (out source : Fin d) (h : Fin d → ℝ) (r : Fin d) :
    (rankOneRead out source).mulVec h r = readRow out r*h source := by
  simp only [rankOneRead, Matrix.mulVec, dotProduct, mul_assoc, ← Finset.mul_sum, read_row_action]

theorem rank_one_read_score {d : ℕ} (feature u v : Fin d) (h g : Fin d → ℝ) :
    (∑ r, (rankOneRead feature u).mulVec h r*(rankOneRead feature v).mulVec g r) = h u*g v := by
  classical
  simp [rank_one_read_action, readRow]

#print axioms fixed_matrix_eval
#print axioms alpha_matrix_eval
#print axioms distance_data_schedule
#print axioms scheduled_distance_query_eval
#print axioms scheduled_distance_key_eval
#print axioms difference_value_alpha_eval
#print axioms rank_one_read_action
#print axioms rank_one_read_score
end GeneralizationCheck
