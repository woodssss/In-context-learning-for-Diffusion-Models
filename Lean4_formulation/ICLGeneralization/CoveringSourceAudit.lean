module

public import ICLGeneralization.SoftmaxStability

@[expose] public section
namespace GeneralizationCheck

/- A one-token negative-logit example tests the comparison used in the cited
   C.5 proof. It does not contradict a separately derived softmax bound. -/
theorem softmax_relu_comparison_counterexample :
    |softmaxReadout 1 (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))-
      softmaxReadout 1 (fun _ => (-1 : ℝ)) (fun _ => (0 : ℝ))| = 1 ∧
    |max 0 (-1 : ℝ)*1-max 0 (-1 : ℝ)*0| = 0 := by
  constructor
  · simp [softmaxReadout,ne_of_gt (Real.exp_pos (-1 : ℝ))]
  · norm_num

theorem cited_multiblock_constant_does_not_shrink (L : ℕ) (hL : 1 ≤ L) :
    (2 : ℝ)^(L^2+1) < (2 : ℝ)^(7*L^2) := by
  have h : L^2+1 < 7*L^2 := by nlinarith
  exact (pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) h)

#print axioms softmax_relu_comparison_counterexample
#print axioms cited_multiblock_constant_does_not_shrink
end GeneralizationCheck
