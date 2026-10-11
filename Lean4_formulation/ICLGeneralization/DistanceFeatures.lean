module

public import ICLGeneralization.RealizationBudget

@[expose] public section

namespace GeneralizationCheck

noncomputable def distanceQueryFeatures (D : ℕ) (M s c : ℝ) (v : Fin D → ℝ) : Fin (D+1) → ℝ :=
  Fin.addCases (fun r => v r/(Real.sqrt 2*s)) (fun _ => Real.sqrt M*c)

noncomputable def distanceKeyFeatures (D : ℕ) (M s c : ℝ) (v : Fin D → ℝ) : Fin (D+1) → ℝ :=
  Fin.addCases (fun r => -v r/(Real.sqrt 2*s)) (fun _ => Real.sqrt M*c)

theorem distance_feature_dot (D : ℕ) (M s c d : ℝ) (hM : 0 ≤ M) (hs : s ≠ 0)
    (v w : Fin D → ℝ) :
    (∑ r, distanceQueryFeatures D M s c v r*distanceKeyFeatures D M s d w r) =
      M*c*d-(∑ r, (v r/s)*(w r/s))/2 := by
  rw [Fin.sum_univ_add]
  simp only [distanceQueryFeatures, distanceKeyFeatures, Fin.addCases_left,
    Fin.addCases_right, Fin.sum_univ_one]
  have hterm (r : Fin D) : (v r/(Real.sqrt 2*s))*(-w r/(Real.sqrt 2*s)) =
      -((v r/s)*(w r/s))/2 := by
    have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  have hroot := Real.sq_sqrt hM
  have hmul : Real.sqrt M*c*(Real.sqrt M*d) = M*c*d := by
    calc
      _ = (Real.sqrt M)^2*c*d := by ring
      _ = _ := by rw [hroot]
  rw [hmul]
  ring

theorem distance_score_is_bilinear_features (n D : ℕ) (M s : ℝ) (hM : 0 ≤ M) (hs : s ≠ 0)
    (H : RealizationState n D) (q k : Fin (n+1)) :
    (∑ r, distanceQueryFeatures D M s 1 (H.difference q) r*
      distanceKeyFeatures D M s 1 (H.difference k) r) = distanceScore n D M s H q k := by
  rw [distance_feature_dot D M s 1 1 hM hs]
  simp [distanceScore]

theorem distance_constant_coefficient_bound (M : ℝ) (hM : 1 ≤ M) : |Real.sqrt M| ≤ M := by
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by linarith : 0 ≤ M)).1
  rw [Real.sq_sqrt (by linarith : 0 ≤ M)]
  nlinarith

#print axioms distance_feature_dot
#print axioms distance_score_is_bilinear_features
#print axioms distance_constant_coefficient_bound
end GeneralizationCheck
