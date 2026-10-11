module

public import ICLGeneralization.RealizationReadout
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section
namespace GeneralizationCheck

theorem softmax_abs_bound (n : ℕ) (hn : 0 < n) (u v : Fin n → ℝ)
    (B : ℝ) (hv : ∀ i, |v i| ≤ B) : |softmaxReadout n u v| ≤ B :=
  abs_le.mpr (softmax_readout_bounds n hn u v B (fun i => abs_le.mp (hv i)))

theorem softmax_value_stability (n : ℕ) (hn : 0 < n) (u v w : Fin n → ℝ)
    (E : ℝ) (hE : ∀ i, |v i-w i| ≤ E) :
    |softmaxReadout n u v-softmaxReadout n u w| ≤ E := by
  have he : softmaxReadout n u v-softmaxReadout n u w =
      softmaxReadout n u (fun i => v i-w i) := by
    unfold softmaxReadout
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact softmax_abs_bound n hn u _ E hE

theorem softmax_path_derivative (n : ℕ) (hn : 0 < n) (u d v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => softmaxReadout n (fun i => u i+t*d i) v)
      (softmaxReadout n (fun i => u i+t*d i) (fun i => v i*d i)-
        softmaxReadout n (fun i => u i+t*d i) v*
        softmaxReadout n (fun i => u i+t*d i) d) t := by
  have he (i : Fin n) : HasDerivAt (fun t : ℝ => Real.exp (u i+t*d i))
      (Real.exp (u i+t*d i)*d i) t := by
    simpa using (((hasDerivAt_id t).mul_const (d i)).const_add (u i)).exp
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => he i)
  have hnum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (he i).const_mul (v i))
  have h := hnum.fun_div hd (ne_of_gt (softmax_denominator_positive n hn _))
  have h' : HasDerivAt (fun t => softmaxReadout n (fun i => u i+t*d i) v)
      (((∑ i, v i*(Real.exp (u i+t*d i)*d i))*(∑ i, Real.exp (u i+t*d i))-
        (∑ i, v i*Real.exp (u i+t*d i))*(∑ i, Real.exp (u i+t*d i)*d i))/
          (∑ i, Real.exp (u i+t*d i))^2) t := by
    simpa only [softmaxReadout, Pi.div_apply] using h
  convert h' using 1
  unfold softmaxReadout
  have hnume : (∑ i, v i*(Real.exp (u i+t*d i)*d i)) =
      ∑ i, (v i*d i)*Real.exp (u i+t*d i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdene : (∑ i, Real.exp (u i+t*d i)*d i) =
      ∑ i, d i*Real.exp (u i+t*d i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hnume,hdene]
  field_simp [ne_of_gt (softmax_denominator_positive n hn (fun i => u i+t*d i))]
  ring_nf
  simp only [mul_comm]

theorem softmax_score_stability (n : ℕ) (hn : 0 < n) (u w v : Fin n → ℝ)
    (B E : ℝ) (hB : 0 ≤ B) (_hE : 0 ≤ E)
    (hv : ∀ i, |v i| ≤ B) (hu : ∀ i, |u i-w i| ≤ E) :
    |softmaxReadout n u v-softmaxReadout n w v| ≤ 2*B*E := by
  let d := fun i => w i-u i
  let f := fun t : ℝ => softmaxReadout n (fun i => u i+t*d i) v
  let f' := fun t : ℝ => softmaxReadout n (fun i => u i+t*d i) (fun i => v i*d i)-
    softmaxReadout n (fun i => u i+t*d i) v*softmaxReadout n (fun i => u i+t*d i) d
  have hd (i : Fin n) : |d i| ≤ E := by simpa only [d, abs_sub_comm] using hu i
  have hp (t : ℝ) : |f' t| ≤ 2*B*E := by
    have h1 := softmax_abs_bound n hn (fun i => u i+t*d i) (fun i => v i*d i) (B*E)
      (fun i => by rw [abs_mul]; exact mul_le_mul (hv i) (hd i) (abs_nonneg _) hB)
    have h2 := softmax_abs_bound n hn (fun i => u i+t*d i) v B hv
    have h3 := softmax_abs_bound n hn (fun i => u i+t*d i) d E hd
    have hprod : |softmaxReadout n (fun i => u i+t*d i) v*
        softmaxReadout n (fun i => u i+t*d i) d| ≤ B*E := by
      rw [abs_mul]
      exact mul_le_mul h2 h3 (abs_nonneg _) hB
    calc
      _ ≤ _ := abs_sub _ _
      _ ≤ B*E+B*E := add_le_add h1 hprod
      _ = _ := by ring
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (f := f) (f' := f') (C := 2*B*E)
    (fun t _ => (softmax_path_derivative n hn u d v t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hp t)
  have hzero : f 0 = softmaxReadout n u v := by simp only [f,zero_mul,add_zero]
  have hone : f 1 = softmaxReadout n w v := by simp only [f,d,one_mul,add_sub_cancel]
  rw [hzero,hone,Real.norm_eq_abs,abs_sub_comm] at hh
  exact hh

theorem softmax_joint_stability (n : ℕ) (hn : 0 < n) (u w v z : Fin n → ℝ)
    (B E F : ℝ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hv : ∀ i, |v i| ≤ B) (hu : ∀ i, |u i-w i| ≤ E) (hz : ∀ i, |v i-z i| ≤ F) :
    |softmaxReadout n u v-softmaxReadout n w z| ≤ 2*B*E+F :=
  (abs_sub_le _ _ _).trans (add_le_add
    (softmax_score_stability n hn u w v B E hB hE hv hu)
    (softmax_value_stability n hn w v z F hz))

#print axioms softmax_abs_bound
#print axioms softmax_value_stability
#print axioms softmax_path_derivative
#print axioms softmax_score_stability
#print axioms softmax_joint_stability
end GeneralizationCheck
