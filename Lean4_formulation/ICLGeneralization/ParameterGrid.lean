module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Tactic

@[expose] public section
namespace GeneralizationCheck

noncomputable def gridSize (κ r : ℝ) : ℕ := Nat.ceil (2*κ/r)+1
noncomputable def gridCode (κ r x : ℝ) : ℕ := Nat.floor ((x+κ)/r)

theorem grid_code_range (κ r x : ℝ) (_hκ : 0 ≤ κ) (hr : 0 < r) (hx : |x| ≤ κ) :
    gridCode κ r x < gridSize κ r := by
  unfold gridCode gridSize
  apply Nat.lt_succ_of_le
  apply le_trans (Nat.floor_mono ?_) (Nat.floor_le_ceil _)
  apply div_le_div_of_nonneg_right _ hr.le
  linarith [(abs_le.mp hx).2]

theorem grid_code_distance (κ r x y : ℝ) (_hκ : 0 ≤ κ) (hr : 0 < r)
    (hx : |x| ≤ κ) (hy : |y| ≤ κ) (hc : gridCode κ r x = gridCode κ r y) : |x-y| ≤ 2*r := by
  have hx0 : 0 ≤ (x+κ)/r := div_nonneg (by linarith [(abs_le.mp hx).1]) hr.le
  have hy0 : 0 ≤ (y+κ)/r := div_nonneg (by linarith [(abs_le.mp hy).1]) hr.le
  have hxl := Nat.floor_le hx0
  have hyl := Nat.floor_le hy0
  have hxu := Nat.lt_floor_add_one ((x+κ)/r)
  have hyu := Nat.lt_floor_add_one ((y+κ)/r)
  change Nat.floor ((x+κ)/r) = Nat.floor ((y+κ)/r) at hc
  rw [← hc] at hyl hyu
  have hxl' := (le_div_iff₀ hr).mp hxl
  have hyl' := (le_div_iff₀ hr).mp hyl
  have hxu' := (div_lt_iff₀ hr).mp hxu
  have hyu' := (div_lt_iff₀ hr).mp hyu
  apply abs_le.mpr
  constructor <;> nlinarith

theorem grid_size_bound (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r) :
    (gridSize κ r : ℝ) ≤ 2*κ/r+2 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 2*κ/r by positivity)
  unfold gridSize
  push_cast
  linarith

theorem finite_parameter_internal_cover {ι : Type*} [Fintype ι]
    (A : Set (ι → ℝ)) (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 < r)
    (hA : ∀ x ∈ A, ∀ i, |x i| ≤ κ) :
    ∃ (N : ℕ) (c : Fin N → ι → ℝ),
      (∀ j, c j ∈ A) ∧ (N : ℝ) ≤ (2*κ/r+2)^Fintype.card ι ∧
      ∀ x ∈ A, ∃ j, ∀ i, |x i-c j i| ≤ 2*r := by
  classical
  let Q := ι → Fin (gridSize κ r)
  let Occupied := {q : Q | ∃ x ∈ A, ∀ i, gridCode κ r (x i) = (q i).val}
  let J := {q : Q // q ∈ Occupied}
  let : Fintype J := Fintype.ofFinite J
  let c : J → ι → ℝ := fun j => Classical.choose j.property
  have hc (j : J) : c j ∈ A ∧ ∀ i, gridCode κ r (c j i) = (j.val i).val :=
    Classical.choose_spec j.property
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => c (e.symm j), fun j => (hc _).1, ?_, ?_⟩
  · have hcard : Fintype.card J ≤ (gridSize κ r)^Fintype.card ι := by
      exact (Fintype.card_subtype_le _).trans_eq (by simp [Q])
    calc
      (Fintype.card J : ℝ) ≤ ((gridSize κ r)^Fintype.card ι : ℕ) := by exact_mod_cast hcard
      _ = (gridSize κ r : ℝ)^Fintype.card ι := by norm_cast
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (grid_size_bound κ r hκ hr) _
  · intro x hx
    let q : Q := fun i => ⟨gridCode κ r (x i), grid_code_range κ r (x i) hκ hr (hA x hx i)⟩
    let j : J := ⟨q, ⟨x,hx,fun _ => rfl⟩⟩
    refine ⟨e j, ?_⟩
    intro i
    change |x i-c (e.symm (e j)) i| ≤ 2*r
    rw [e.symm_apply_apply]
    apply grid_code_distance κ r _ _ hκ hr (hA x hx i) (hA _ (hc j).1 i)
    exact (hc j).2 i |>.symm

#print axioms grid_code_range
#print axioms grid_code_distance
#print axioms grid_size_bound
#print axioms finite_parameter_internal_cover
end GeneralizationCheck
