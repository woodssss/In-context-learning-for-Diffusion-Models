module

public import ICLGeneralization.NativeParameterBridge
public import ICLGeneralization.LemmaFourFixedSampling

@[expose] public section
namespace GeneralizationCheck

theorem native_head_bounded {n D : ℕ} (T : FiveBlockTransformer n D) (κ : ℝ) (hκ : 0 ≤ κ)
    (hT : T.Bounded κ) (k : Fin 5) (i : Fin n) : (nativeHead T k i).Bounded κ := by
  unfold nativeHead
  split_ifs
  · exact hT.1 _ _
  · exact hT.2.2.1
  · have h := fixed_matrix_bounded (0 : Matrix (Fin (embedWidth D)) (Fin (embedWidth D)) ℝ) κ hκ
      (zero_matrix_bound _ _ κ hκ)
    exact ⟨h,h,h⟩

theorem native_ffn_bounded {n D : ℕ} (T : FiveBlockTransformer n D) (κ : ℝ) (hT : T.Bounded κ)
    (k : Fin 5) : (nativeFFN T k).Bounded κ := by
  apply cast_six_ffn_bounded
  split_ifs
  · exact hT.2.1 _
  · exact hT.2.2.2

theorem native_kind_bounded {w : ℕ} (H : ScheduledHead w) (κ : ℝ) (hH : H.Bounded κ)
    (j : Fin 3) : (nativeMatrixKind H j).Bounded κ := by
  fin_cases j
  · exact hH.1
  · exact hH.2.1
  · exact hH.2.2

theorem native_layout_bounded {n D : ℕ} (T : FiveBlockTransformer n D) (κ : ℝ) (hκ : 0 ≤ κ)
    (hT : T.Bounded κ) : (nativeLayout T).Bounded κ :=
  ⟨fun k i h r c => (native_kind_bounded _ κ (native_head_bounded T κ hκ hT k i) h).2.1 r c,
   fun k i h r c => (native_kind_bounded _ κ (native_head_bounded T κ hκ hT k i) h).2.2 r c⟩

theorem native_parameter_bounded {n D : ℕ} (T : FiveBlockTransformer n D) (κ : ℝ) (hκ : 1 ≤ κ)
    (hT : T.Bounded κ) : ∀ p, |nativeParameter T p| ≤ κ := by
  intro p
  rcases p with ⟨r,c⟩|p
  · exact (read_row_abs_bound _ _).trans hκ
  · rcases p with ⟨k,i,h,r,c⟩|p
    · exact (native_kind_bounded _ κ (native_head_bounded T κ (by linarith) hT k i) h).1 r c
    · rcases p with ⟨k,j,p⟩|r
      · have hF := native_ffn_bounded T κ hT k
        rcases p with ⟨r,c⟩|r
        · change |nativeAffine (nativeFFN T k) j r c| ≤ κ
          unfold nativeAffine
          split_ifs
          · exact hF.1 r c
          · exact hF.2.2.2.2.1 r c
          · exact hF.2.2.1 r c
        · change |nativeBias (nativeFFN T k) j r| ≤ κ
          unfold nativeBias
          split_ifs
          · exact hF.2.1 r
          · exact hF.2.2.2.2.2 r
          · exact hF.2.2.2.1 r
      · exact (read_row_abs_bound _ _).trans hκ

theorem native_pe_bound (n D : ℕ) : ∀ q r, |nativePE n D q r| ≤ 1 := by
  intro q r
  refine Fin.addCases (fun r => ?_) (fun r => ?_) r
  · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r <;> simp [nativePE,packState,packCore,initialState]
    · refine Fin.addCases (fun r => ?_) (fun r => ?_) r
      · simp [nativePE,packState,packCore,initialState]
      · fin_cases r <;> simp [nativePE,packState,packCore,initialState]
  · fin_cases r
    · simpa [nativePE,packState] using Real.abs_cos_le_one (tokenAngle (n+1) q)
    · simpa [nativePE,packState] using Real.abs_sin_le_one (tokenAngle (n+1) q)
    · simp [nativePE,packState]

theorem fixed_time_layout_ext {w L m : ℕ} (A B : FixedTimeLayout w L m)
    (ha : A.alpha=B.alpha) (hr : A.reciprocal=B.reciprocal) : A=B := by
  cases A; cases B; cases ha; cases hr; rfl

theorem kernel_layout_independent {n D : ℕ} (j j' : Fin D) (M M' b b' : ℝ) :
    nativeLayout (kernelTransformer n D j M b) = nativeLayout (kernelTransformer n D j' M' b') := by
  apply fixed_time_layout_ext
  all_goals
    funext k i h r c
    fin_cases k <;> fin_cases h
    all_goals simp [nativeLayout,nativeHead,nativeMatrixKind,kernelTransformer,copyScheduledHead,
      scheduledDistanceQuery,scheduledDistanceKey,fixedMatrix,alphaMatrix,zeroScheduledHead]

noncomputable def nativeVectorParameter {n D : ℕ} (T : Fin D → FiveBlockTransformer n D) :
    VectorFixedTimeParameter D (embedWidth D) 5 6 n → ℝ := fun p => nativeParameter (T p.1) p.2

theorem native_gaussian_mean {Time : Type*} (n D : ℕ) (hn : 0<n) (S : Set (KernelSpace D))
    (a s : Time → ℝ) (C : ℝ) (T : Fin D → FiveBlockTransformer n D)
    (p : GaussianCoverSample Time n D S) (j : Fin D) :
    generalMean (gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s C
      (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation)
      (vectorFixedTimeLift (fun j => nativeLayout (T j)) (nativeVectorParameter T)) p j =
    (T j).eval (a p.1) (s p.1) (fun i r => (p.2.2 i).val r)
      (fun r => a p.1*p.2.1.1.val r+s p.1*p.2.1.2 r) := by
  change generalTransformer (nativeLift (T j)) (nativePE n D) (fun _ _ => 1)
    (gaussianRawInput n D a s p) nativeSoftmax nativeActivation Fin.castSucc (a p.1) (s p.1) (Fin.last n) = _
  have hi : gaussianRawInput n D a s p = nativeRawInput (fun i r => (p.2.2 i).val r)
      (fun r => a p.1*p.2.1.1.val r+s p.1*p.2.1.2 r) := by
    funext q r
    simp only [gaussianRawInput,nativeRawInput,initialState]
    split_ifs <;> rfl
  rw [hi,native_transformer_evaluation hn]

theorem native_gaussian_cover_membership {Time : Type*} (n D : ℕ) (hn : 0<n) (S : Set (KernelSpace D))
    (a s : Time → ℝ) (C κ R : ℝ) (hκ : 1≤κ) (T : Fin D → FiveBlockTransformer n D)
    (hT : ∀ j, InScalarTransformerClass (T j) R κ) :
    nativeVectorParameter T ∈ admissibleFixedTimeParameters
      (gaussianLossSetup n D (embedWidth D) 5 6 n (S:=S) a s C
        (nativePE n D) (fun _ _ => 1) nativeSoftmax nativeActivation)
      (fun j => nativeLayout (T j)) κ R := by
  constructor
  · intro p
    exact native_parameter_bounded (T p.1) κ hκ (hT p.1).1 p.2
  · intro p j
    rw [native_gaussian_mean n D hn S a s C T p j]
    exact (hT j).2 _ _ _ _

theorem fixed_concrete_vector_parameter_budget (n D : ℕ) (hn : 1≤n) (hD : 1≤D) :
    D*fixedTimeParameterCount D (2*D+6) 5 6 n ≤ 3136*n*D^3 := by
  have hw : 2*D+6 ≤ 8*D := by omega
  have hwsq : (2*D+6)^2 ≤ 64*D^2 := by nlinarith
  have hDn : D^2 ≤ n*D^2 := by simpa only [one_mul] using Nat.mul_le_mul_right (D^2) hn
  have hDsq : D ≤ D^2 := by nlinarith
  have hcount : fixedTimeParameterCount D (2*D+6) 5 6 n ≤ 3136*n*D^2 := by
    unfold fixedTimeParameterCount
    have h1 := Nat.mul_le_mul_left (15*n+30) hwsq
    have h2 := Nat.mul_le_mul_right (D+31) hw
    nlinarith
  have hh := Nat.mul_le_mul_left D hcount
  convert hh using 1
  ring

#print axioms native_head_bounded
#print axioms native_ffn_bounded
#print axioms native_kind_bounded
#print axioms native_layout_bounded
#print axioms native_parameter_bounded
#print axioms native_pe_bound
#print axioms fixed_time_layout_ext
#print axioms kernel_layout_independent
#print axioms native_gaussian_mean
#print axioms native_gaussian_cover_membership
#print axioms fixed_concrete_vector_parameter_budget
end GeneralizationCheck
