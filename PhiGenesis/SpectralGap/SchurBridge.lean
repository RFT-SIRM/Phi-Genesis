import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.SignedLaplacianMatrix
import PhiGenesis.SpectralGap.RecursiveSierpinskiFaces

/-!
# Bridge from the graph matrix to the Schur recursion (first steps)

B0: the signed matrix is the vertex-gauge conjugate of the signless matrix.
B2a: corner coordinates of level `m+1` faces are translates of level `m` ones.
-/

namespace PhiGenesis.SpectralGap

/-- Indicator of the two endpoints of an edge, without gauge signs. -/
noncomputable def sgEdgeIndicator (m : Nat)
    (e : SGVertex m × SGVertex m) (v : SGVertex m) : ℝ :=
  (if v = e.1 then 1 else 0) + (if v = e.2 then 1 else 0)

/-- Signless Laplacian `D + A` of the level-`m` graph, assembled edge by edge. -/
noncomputable def sgSignlessLaplacianMatrix (m : Nat) :
    Matrix (SGVertex m) (SGVertex m) ℝ :=
  fun u v =>
    ∑ e ∈ faceGraphEdges (sgFaceA m) (sgFaceB m) (sgFaceC m),
      sgEdgeIndicator m e u * sgEdgeIndicator m e v

/-- Edge vectors differ from the unsigned indicators by the gauge factor. -/
theorem sgSignedEdgeVector_eq_gauge_mul (m : Nat)
    (e : SGVertex m × SGVertex m) (v : SGVertex m) :
    sgSignedEdgeVector m e v =
      sgVertexGauge e.1 * sgVertexGauge v * sgEdgeIndicator m e v := by
  classical
  have h1 := sgVertexGauge_sq e.1
  have h2 := sgVertexGauge_sq e.2
  unfold sgSignedEdgeVector sgEdgeIndicator
  by_cases ha : v = e.1
  · by_cases hb : v = e.2
    · have hab : e.2 = e.1 := hb.symm.trans ha
      subst ha
      rw [hab]
      simp
      nlinarith [h1]
    · subst ha
      simp [hb]
      nlinarith [h1]
  · by_cases hb : v = e.2
    · subst hb
      simp [ha]
    · simp [ha, hb]

/-- B0: the signed matrix is the gauge conjugate of the signless one. -/
theorem sgSignedLaplacianMatrix_eq_gauge_conj (m : Nat) :
    sgSignedLaplacianMatrix m =
      Matrix.diagonal (fun v => sgVertexGauge v) * sgSignlessLaplacianMatrix m *
        Matrix.diagonal (fun v => sgVertexGauge v) := by
  classical
  ext u v
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul,
    sgSignedLaplacianMatrix, sgSignlessLaplacianMatrix]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  have h1 := sgVertexGauge_sq e.1
  simp only [sgSignedEdgeVector_eq_gauge_mul]
  linear_combination
    (sgVertexGauge u * sgVertexGauge v * sgEdgeIndicator m e u *
      sgEdgeIndicator m e v) * h1

/-- B2a: level-`m+1` face corners are translates of level-`m` corners. -/
theorem sgFaceCornerCoords_succ (m : Nat) (w : Fin (m + 1) → Fin 3)
    (c : TriangleCorner) :
    sgFaceCornerCoords (m + 1) (w, c) =
      sgAddOffset m (w 0) (sgFaceCornerCoords m (sgFaceTail w, c)) := by
  cases c <;> simp [sgFaceCornerCoords, sgFaceOrigin, sgAddOffset] <;> omega

end PhiGenesis.SpectralGap
