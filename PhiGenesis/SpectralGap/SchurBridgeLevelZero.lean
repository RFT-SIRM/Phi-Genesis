import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurBridge

/-!
# Bridge, step B1: the level-zero matrix

At level 0 there is a single triangle. Its signless Laplacian has diagonal 2 and
off-diagonal 1, so `Q_0 - lam I` has the Schur-recursion start state `(2 - lam, 1)`.
-/

namespace PhiGenesis.SpectralGap

/-- The unique level-zero face address. -/
private def sgF0 : Fin 0 → Fin 3 := fun i => i.elim0

private theorem sgFace0_unique (f : Fin 0 → Fin 3) : f = sgF0 := by
  funext i
  exact i.elim0

private def v0A : SGVertex 0 := sgCornerVertex 0 (sgF0, .leftBase)
private def v0B : SGVertex 0 := sgCornerVertex 0 (sgF0, .rightBase)
private def v0C : SGVertex 0 := sgCornerVertex 0 (sgF0, .apex)

private theorem v0A_ne_v0B : v0A ≠ v0B := by
  intro h
  have := congrArg (fun v : SGVertex 0 => v.1) h
  simp [v0A, v0B, sgCornerVertex, sgFaceCornerCoords, sgFaceOrigin] at this

private theorem v0A_ne_v0C : v0A ≠ v0C := by
  intro h
  have := congrArg (fun v : SGVertex 0 => v.1) h
  simp [v0A, v0C, sgCornerVertex, sgFaceCornerCoords, sgFaceOrigin] at this

private theorem v0B_ne_v0C : v0B ≠ v0C := by
  intro h
  have := congrArg (fun v : SGVertex 0 => v.1) h
  simp [v0B, v0C, sgCornerVertex, sgFaceCornerCoords, sgFaceOrigin] at this

private theorem sgVertex0_cases (u : SGVertex 0) :
    u = v0A ∨ u = v0B ∨ u = v0C := by
  obtain ⟨⟨f, c⟩, rfl⟩ := sgCornerVertex_surjective 0 u
  have hf := sgFace0_unique f
  subst hf
  cases c
  · left; rfl
  · right; left; rfl
  · right; right; rfl

private theorem faceGraphEdges_zero :
    faceGraphEdges (sgFaceA 0) (sgFaceB 0) (sgFaceC 0) =
      {(v0A, v0B), (v0A, v0C), (v0B, v0C)} := by
  ext e
  simp only [faceGraphEdges, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨f, edge⟩, rfl⟩
    have hf := sgFace0_unique f
    subst hf
    cases edge <;>
      simp [faceEdgeEndpoints, sgFaceA, sgFaceB, sgFaceC, v0A, v0B, v0C]
  · rintro (rfl | rfl | rfl)
    · exact ⟨(sgF0, .base), rfl⟩
    · exact ⟨(sgF0, .left), rfl⟩
    · exact ⟨(sgF0, .right), rfl⟩

/-- B1: the level-zero signless Laplacian has diagonal 2 and off-diagonal 1. -/
theorem sgSignlessLaplacianMatrix_zero (u v : SGVertex 0) :
    sgSignlessLaplacianMatrix 0 u v = if u = v then 2 else 1 := by
  rw [sgSignlessLaplacianMatrix, faceGraphEdges_zero]
  have hAB := v0A_ne_v0B
  have hAC := v0A_ne_v0C
  have hBC := v0B_ne_v0C
  rcases sgVertex0_cases u with rfl | rfl | rfl <;>
    rcases sgVertex0_cases v with rfl | rfl | rfl <;>
    simp [Finset.sum_insert, sgEdgeIndicator, hAB, hAB.symm, hAC, hAC.symm,
      hBC, hBC.symm] <;> norm_num

/-- The shifted level-zero matrix has the Schur start state `(2 - lam, 1)`. -/
theorem sgSignlessShifted_zero (lam : ℝ) (u v : SGVertex 0) :
    (sgSignlessLaplacianMatrix 0 - lam • (1 : Matrix (SGVertex 0) (SGVertex 0) ℝ)) u v =
      if u = v then 2 - lam else 1 := by
  by_cases h : u = v <;>
    simp [Matrix.sub_apply, Matrix.one_apply, sgSignlessLaplacianMatrix_zero, h]

end PhiGenesis.SpectralGap
