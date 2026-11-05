import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.SignedGaugeEnergy

/-!
# Matrix realization of the signed gasket energy

The finite matrix is assembled as a sum of rank-one edge contributions.
Its quadratic form is exactly the already-proved signed graph energy.  This
file then derives the lower bound on every real eigenvalue represented by a
nonzero eigenvector.  The result concerns the explicit local-face signing.
-/

namespace PhiGenesis.SpectralGap

/-- The edge vector whose two endpoint coefficients are one and the
local gauge product. -/
noncomputable def sgSignedEdgeVector (m : Nat)
    (e : SGVertex m × SGVertex m) (v : SGVertex m) : ℝ :=
  (if v = e.1 then 1 else 0) +
    (if v = e.2 then sgVertexGauge e.1 * sgVertexGauge e.2 else 0)

/-- Summing an edge vector against a vertex function recovers its signed
endpoint sum. -/
theorem sgSignedEdgeVector_sum (m : Nat)
    (e : SGVertex m × SGVertex m) (x : SGVertex m → ℝ) :
    (∑ v : SGVertex m, sgSignedEdgeVector m e v * x v) =
      x e.1 + sgVertexGauge e.1 * sgVertexGauge e.2 * x e.2 := by
  classical
  have hindicator (a : SGVertex m) (c : ℝ) :
      (∑ v : SGVertex m, (if v = a then c else 0) * x v) = c * x a := by
    calc
      (∑ v : SGVertex m, (if v = a then c else 0) * x v) =
          ∑ v : SGVertex m, (if v = a then c * x a else 0) := by
            apply Finset.sum_congr rfl
            intro v hv
            by_cases h : v = a <;> simp [h]
      _ = c * x a := by simp
  calc
    (∑ v : SGVertex m, sgSignedEdgeVector m e v * x v) =
        ∑ v : SGVertex m,
          ((if v = e.1 then 1 else 0) * x v +
            (if v = e.2 then sgVertexGauge e.1 * sgVertexGauge e.2 else 0) * x v) := by
          unfold sgSignedEdgeVector
          apply Finset.sum_congr rfl
          intro v hv
          ring
    _ = (∑ v : SGVertex m, (if v = e.1 then 1 else 0) * x v) +
        ∑ v : SGVertex m,
          (if v = e.2 then sgVertexGauge e.1 * sgVertexGauge e.2 else 0) * x v := by
          rw [Finset.sum_add_distrib]
    _ = x e.1 + sgVertexGauge e.1 * sgVertexGauge e.2 * x e.2 := by
          rw [hindicator e.1 1,
              hindicator e.2 (sgVertexGauge e.1 * sgVertexGauge e.2)]
          norm_num

/-- The signed Laplacian matrix is the sum of rank-one matrices associated
with the signed edge vectors.  Its entries are symmetric by construction. -/
noncomputable def sgSignedLaplacianMatrix (m : Nat) :
    Matrix (SGVertex m) (SGVertex m) ℝ :=
  fun u v =>
    ∑ e ∈ faceGraphEdges (sgFaceA m) (sgFaceB m) (sgFaceC m),
      sgSignedEdgeVector m e u * sgSignedEdgeVector m e v

/-- The signed Laplacian matrix is symmetric. -/
theorem sgSignedLaplacianMatrix_symmetric (m : Nat) :
    ∀ u v : SGVertex m,
      sgSignedLaplacianMatrix m u v = sgSignedLaplacianMatrix m v u := by
  intro u v
  simp [sgSignedLaplacianMatrix, mul_comm]

/-- Finite sums of rank-one matrices have the expected quadratic form. -/
private theorem sum_outerProduct_quadratic
    {V E : Type*} [Fintype V]
    (s : Finset E) (b : E → V → ℝ) (x : V → ℝ) :
    (∑ v : V, x v *
      ∑ w : V, (∑ e ∈ s, b e v * b e w) * x w) =
      ∑ e ∈ s, (∑ v : V, b e v * x v) ^ 2 := by
  classical
  calc
    (∑ v : V, x v *
        ∑ w : V, (∑ e ∈ s, b e v * b e w) * x w) =
      ∑ v : V, x v *
        ∑ e ∈ s, b e v * (∑ w : V, b e w * x w) := by
          apply Finset.sum_congr rfl
          intro v hv
          congr 1
          calc
            (∑ w : V, (∑ e ∈ s, b e v * b e w) * x w) =
                ∑ w : V, ∑ e ∈ s, (b e v * b e w) * x w := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  rw [Finset.sum_mul]
            _ = ∑ e ∈ s, ∑ w : V, (b e v * b e w) * x w := by
                  rw [Finset.sum_comm]
            _ = ∑ e ∈ s, b e v * (∑ w : V, b e w * x w) := by
                  apply Finset.sum_congr rfl
                  intro e he
                  calc
                    (∑ w : V, (b e v * b e w) * x w) =
                        ∑ w : V, b e v * (b e w * x w) := by
                          apply Finset.sum_congr rfl
                          intro w hw
                          ring
                    _ = b e v * ∑ w : V, b e w * x w := by
                          rw [← Finset.mul_sum]
    _ = ∑ e ∈ s, ∑ v : V,
          x v * (b e v * (∑ w : V, b e w * x w)) := by
          calc
            (∑ v : V, x v *
                ∑ e ∈ s, b e v * (∑ w : V, b e w * x w)) =
              ∑ v : V, ∑ e ∈ s,
                x v * (b e v * (∑ w : V, b e w * x w)) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  rw [Finset.mul_sum]
            _ = ∑ e ∈ s, ∑ v : V,
                x v * (b e v * (∑ w : V, b e w * x w)) := by
                  rw [Finset.sum_comm]
    _ = ∑ e ∈ s,
          (∑ v : V, b e v * x v) *
            (∑ w : V, b e w * x w) := by
          apply Finset.sum_congr rfl
          intro e he
          calc
            (∑ v : V, x v *
                (b e v * (∑ w : V, b e w * x w))) =
              ∑ v : V, (b e v * x v) *
                (∑ w : V, b e w * x w) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  ring
            _ = (∑ v : V, b e v * x v) *
                (∑ w : V, b e w * x w) := by
                  rw [Finset.sum_mul]
    _ = ∑ e ∈ s, (∑ v : V, b e v * x v) ^ 2 := by
          apply Finset.sum_congr rfl
          intro e he
          ring

/-- The matrix quadratic form is exactly the signed edge energy. -/
theorem sgSignedLaplacianMatrix_quadraticForm (m : Nat)
    (x : SGVertex m → ℝ) :
    (∑ u : SGVertex m, x u *
      ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v) =
        sgSignedGraphEnergy m x := by
  classical
  calc
    (∑ u : SGVertex m, x u *
        ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v) =
      ∑ e ∈ faceGraphEdges (sgFaceA m) (sgFaceB m) (sgFaceC m),
        (∑ u : SGVertex m, sgSignedEdgeVector m e u * x u) ^ 2 := by
          simpa [sgSignedLaplacianMatrix] using
            (sum_outerProduct_quadratic
              (s := faceGraphEdges (sgFaceA m) (sgFaceB m) (sgFaceC m))
              (b := sgSignedEdgeVector m) (x := x))
    _ = sgSignedGraphEnergy m x := by
          unfold sgSignedGraphEnergy
          apply Finset.sum_congr rfl
          intro e he
          rw [sgSignedEdgeVector_sum]

/-- A nonzero real eigenvector of the signed Laplacian has eigenvalue at
least one.  The eigenvector equation is written row-by-row, i.e. as the
ordinary matrix-vector equation for sgSignedLaplacianMatrix. -/
theorem sgSignedLaplacianMatrix_eigenvalue_ge_one (m : Nat)
    (eigval : ℝ) (x : SGVertex m → ℝ)
    (hEigen : ∀ u : SGVertex m,
      (∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v) = eigval * x u)
    (hx : x ≠ 0) :
    1 ≤ eigval := by
  classical
  let mass : ℝ := ∑ v : SGVertex m, (x v) ^ 2
  have hmass_pos : 0 < mass := by
    have hxSome : ∃ v : SGVertex m, x v ≠ 0 := by
      by_contra hnone
      push_neg at hnone
      apply hx
      funext v
      exact hnone v
    obtain ⟨v, hv⟩ := hxSome
    have hsq : 0 < (x v) ^ 2 := sq_pos_of_ne_zero hv
    have hsingle :
        (x v) ^ 2 ≤ ∑ w : SGVertex m, (x w) ^ 2 :=
      Finset.single_le_sum
        (fun w hw => sq_nonneg (x w)) (Finset.mem_univ v)
    dsimp [mass]
    exact lt_of_lt_of_le hsq hsingle
  have hmass_le : mass ≤ eigval * mass := by
    dsimp [mass]
    calc
      (∑ v : SGVertex m, (x v) ^ 2) ≤ sgSignedGraphEnergy m x :=
        sgSignedGraphEnergy_lower_bound m x
      _ = ∑ u : SGVertex m, x u *
          ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v :=
        (sgSignedLaplacianMatrix_quadraticForm m x).symm
      _ = ∑ u : SGVertex m, x u * (eigval * x u) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hEigen u]
      _ = ∑ u : SGVertex m, eigval * (x u) ^ 2 := by
        apply Finset.sum_congr rfl
        intro u hu
        ring
      _ = eigval * ∑ u : SGVertex m, (x u) ^ 2 := by
        rw [Finset.mul_sum]
  dsimp [mass] at hmass_pos hmass_le
  nlinarith


/-- Signed edge-incidence matrix for the local-face signing.
Rows are indexed by recursive face-edge slots, so each row is the vector
with coefficient one at the first endpoint and the gauge product at the
second endpoint. -/
noncomputable def sgSignedIncidenceMatrix (m : Nat) :
    Matrix ((Fin m → Fin 3) × TriangleEdge) (SGVertex m) ℝ :=
  fun p v =>
    sgSignedEdgeVector m
      (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p) v

/-- The signed Laplacian already defined above is exactly the Gram matrix
of its signed edge-incidence matrix: L = Bᵀ B.  This identifies the matrix
with the standard signed Laplacian for the convention sigma = -s. -/
theorem sgSignedLaplacianMatrix_eq_incidenceGram (m : Nat) :
    sgSignedLaplacianMatrix m =
      (sgSignedIncidenceMatrix m).transpose * sgSignedIncidenceMatrix m := by
  classical
  ext u v
  simp only [sgSignedLaplacianMatrix, sgSignedIncidenceMatrix,
    Matrix.mul_apply, Matrix.transpose_apply]
  change
    (∑ e ∈ Finset.univ.image
      (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)),
        sgSignedEdgeVector m e u * sgSignedEdgeVector m e v) =
      ∑ p : (Fin m → Fin 3) × TriangleEdge,
        sgSignedEdgeVector m
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p) u *
        sgSignedEdgeVector m
          (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p) v
  symm
  have hinj : Set.InjOn
      (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m))
      (↑(Finset.univ : Finset ((Fin m → Fin 3) × TriangleEdge))) := by
    intro p hp q hq hpq
    exact sgFaceEdgeEndpoints_injective m hpq
  rw [Finset.sum_image hinj]

/-- The matrix lower bound in Rayleigh form: every real vector has
quadratic energy at least its squared Euclidean norm. -/
theorem sgSignedLaplacianMatrix_quadraticForm_ge_norm (m : Nat)
    (x : SGVertex m → ℝ) :
    (∑ v : SGVertex m, (x v) ^ 2) ≤
      ∑ u : SGVertex m, x u *
        ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v := by
  calc
    (∑ v : SGVertex m, (x v) ^ 2) ≤ sgSignedGraphEnergy m x :=
      sgSignedGraphEnergy_lower_bound m x
    _ = ∑ u : SGVertex m, x u *
        ∑ v : SGVertex m, sgSignedLaplacianMatrix m u v * x v :=
      (sgSignedLaplacianMatrix_quadraticForm m x).symm

end PhiGenesis.SpectralGap
