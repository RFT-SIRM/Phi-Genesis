import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSlots

namespace PhiGenesis.SpectralGap

/-- Row of the shifted signless matrix applied to `x`. -/
noncomputable def sgShiftedRow (m : Nat) (lam : ℝ)
    (x : SGVertex m → ℝ) (v : SGVertex m) : ℝ :=
  ∑ w, (sgSignlessLaplacianMatrix m -
    lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v w * x w

/-- C: gluing child functions into a parent function, given consistency on shared vertices. -/
theorem sgGlue_exists (m : Nat) (f : Fin 3 → SGVertex m → ℝ)
    (hcons : ∀ i a j b, sgChildVertex m i a = sgChildVertex m j b → f i a = f j b) :
    ∃ x : SGVertex (m + 1) → ℝ, ∀ i a, x (sgChildVertex m i a) = f i a := by
  classical
  have hs := sgChildVertex_surjective_union m
  refine ⟨fun v => f (Classical.choose (hs v)).1 (Classical.choose (hs v)).2, ?_⟩
  intro i a
  exact hcons _ _ _ _ (Classical.choose_spec (hs (sgChildVertex m i a)))

/-- D: shared vertices of two children are shared corners with the same boundary index. -/
theorem sgChildVertex_eq_cases (m : Nat) (i j : Fin 3) (a b : SGVertex m)
    (h : sgChildVertex m i a = sgChildVertex m j b) :
    (i = j ∧ a = b) ∨
      ∃ c c' : TriangleCorner,
        a = sgLevelOuterCorner m c ∧ b = sgLevelOuterCorner m c' ∧
          sgChildCornerBoundaryIndex i c = sgChildCornerBoundaryIndex j c' := by
  sorry

/-- A: row at an outer corner of the parent equals the row at that corner of its only child. -/
theorem sgShiftedRow_outerCorner (m : Nat) (lam : ℝ)
    (x : SGVertex (m + 1) → ℝ) (i : Fin 3) (c : TriangleCorner)
    (hc : sgChildCornerBoundaryIndex i c = 0 ∨ sgChildCornerBoundaryIndex i c = 1 ∨
      sgChildCornerBoundaryIndex i c = 2) :
    sgShiftedRow (m + 1) lam x (sgChildVertex m i (sgLevelOuterCorner m c)) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m i v)) (sgLevelOuterCorner m c) := by
  sorry

/-- B: row at midpoint 01 is the sum of the two child corner rows plus `lam * x(mid)`. -/
theorem sgShiftedRow_midpoint01 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint01 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 0 v))
        (sgLevelOuterCorner m TriangleCorner.rightBase) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 1 v))
        (sgLevelOuterCorner m TriangleCorner.leftBase) +
      lam * x (sgParentMidpoint01 m) := by
  sorry

theorem sgShiftedRow_midpoint02 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint02 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 0 v))
        (sgLevelOuterCorner m TriangleCorner.apex) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 2 v))
        (sgLevelOuterCorner m TriangleCorner.leftBase) +
      lam * x (sgParentMidpoint02 m) := by
  sorry

theorem sgShiftedRow_midpoint12 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint12 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 1 v))
        (sgLevelOuterCorner m TriangleCorner.apex) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 2 v))
        (sgLevelOuterCorner m TriangleCorner.rightBase) +
      lam * x (sgParentMidpoint12 m) := by
  sorry

end PhiGenesis.SpectralGap
