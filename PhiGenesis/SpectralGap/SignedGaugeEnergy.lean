import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.RecursiveSierpinskiFaces

/-!
# Gauge identity and signed energy lower bound

The local-face signing is a vertex gauge of the unsigned pair energy.
For lattice coordinates `(i,j)`, the gauge is `(-1)^j`. The local edge
sign is positive on the horizontal edge of each upward face and negative
on its other two edges. In the repository convention `sigma = 1 - 2*x`
and `L = D - A_sigma`, this is `sigma = -s`, hence `L = D + A_s`.
-/

namespace PhiGenesis.SpectralGap

/-- The alternating gauge attached to a horizontal lattice row. -/
def sgRowGauge (j : Nat) : ℝ := if j % 2 = 0 then 1 else -1

/-- Every row-gauge value is a sign. -/
theorem sgRowGauge_sq (j : Nat) : (sgRowGauge j) ^ 2 = 1 := by
  unfold sgRowGauge
  split_ifs <;> norm_num

/-- Consecutive rows have opposite gauge signs. -/
theorem sgRowGauge_mul_succ (j : Nat) :
    sgRowGauge j * sgRowGauge (j + 1) = -1 := by
  by_cases hj : j % 2 = 0
  · have hnext : (j + 1) % 2 = 1 := by omega
    simp [sgRowGauge, hj, hnext]
  · have hparity : j % 2 = 1 := by omega
    have hnext : (j + 1) % 2 = 0 := by omega
    simp [sgRowGauge, hparity, hnext]

/-- Vertex gauge `epsilon(i,j) = (-1)^j` on the recursive gasket. -/
def sgVertexGauge {m : Nat} (v : SGVertex m) : ℝ :=
  sgRowGauge v.1.2

/-- The square of each vertex gauge is one. -/
theorem sgVertexGauge_sq {m : Nat} (v : SGVertex m) :
    (sgVertexGauge v) ^ 2 = 1 := by
  exact sgRowGauge_sq v.1.2

/-- The local sign assigned to an upward-face edge slot. -/
def sgFaceSlotSign (m : Nat)
    (p : (Fin m → Fin 3) × TriangleEdge) : ℝ :=
  match p.2 with
  | .base => 1
  | .left => -1
  | .right => -1

/-- The local face sign is exactly the product of the endpoint gauges. -/
theorem sgFaceSlotSign_eq_rowGaugeProduct (m : Nat)
    (p : (Fin m → Fin 3) × TriangleEdge) :
    sgFaceSlotSign m p =
      sgRowGauge (sgFaceEdgeCoords m p).1.2 *
        sgRowGauge (sgFaceEdgeCoords m p).2.2 := by
  rcases p with ⟨f, e⟩
  cases e
  · simp [sgFaceSlotSign, sgFaceEdgeCoords, sgFaceCornerCoords, sgRowGauge_mul_self]
  · simp [sgFaceSlotSign, sgFaceEdgeCoords, sgFaceCornerCoords, sgRowGauge_mul_succ]
  · simp [sgFaceSlotSign, sgFaceEdgeCoords, sgFaceCornerCoords, sgRowGauge_mul_succ]

/-- Rewriting the local face sign through the subtype endpoints gives the
same product of vertex gauges on the actual finite graph vertices. -/
theorem sgFaceSlotSign_eq_vertexGaugeProduct (m : Nat)
    (p : (Fin m → Fin 3) × TriangleEdge) :
    sgFaceSlotSign m p =
      sgVertexGauge ((faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1) *
        sgVertexGauge ((faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2) := by
  have h := sgFaceSlotSign_eq_rowGaugeProduct m p
  rw [sgFaceEdgeCoords_eq_val m p] at h
  simpa [sgVertexGauge] using h

/-- The signed edge quadratic term is the gauged unsigned pair term. -/
theorem sgSignedEdgeTerm_eq_gauge {m : Nat} (x : SGVertex m → ℝ)
    (u v : SGVertex m) :
    (x u + sgVertexGauge u * sgVertexGauge v * x v) ^ 2 =
      (sgVertexGauge u * x u + sgVertexGauge v * x v) ^ 2 := by
  have hgu : sgVertexGauge u * sgVertexGauge u = 1 := by
    simpa [pow_two] using sgVertexGauge_sq u
  have hinner :
      x u + sgVertexGauge u * sgVertexGauge v * x v =
        sgVertexGauge u *
          (sgVertexGauge u * x u + sgVertexGauge v * x v) := by
    calc
      x u + sgVertexGauge u * sgVertexGauge v * x v =
          (sgVertexGauge u * sgVertexGauge u) * x u +
            (sgVertexGauge u * sgVertexGauge v) * x v := by
              rw [hgu]
      _ = sgVertexGauge u *
            (sgVertexGauge u * x u + sgVertexGauge v * x v) := by ring
  calc
    (x u + sgVertexGauge u * sgVertexGauge v * x v) ^ 2 =
        (sgVertexGauge u *
          (sgVertexGauge u * x u + sgVertexGauge v * x v)) ^ 2 :=
      congrArg (fun z : ℝ => z ^ 2) hinner
    _ = (sgVertexGauge u * x u + sgVertexGauge v * x v) ^ 2 := by
      rw [mul_pow, sgVertexGauge_sq]
      ring

/-- Signed quadratic energy on the finite graph, each edge counted once.
Its edge sign is the local-face signing `s_uv = epsilon(u) epsilon(v)`. -/
def sgSignedGraphEnergy (m : Nat) (x : SGVertex m → ℝ) : ℝ :=
  ∑ e ∈ faceGraphEdges (sgFaceA m) (sgFaceB m) (sgFaceC m),
    (x e.1 + sgVertexGauge e.1 * sgVertexGauge e.2 * x e.2) ^ 2

/-- The signed graph energy is the ordinary pair energy after the vertex
gauge transformation. -/
theorem sgSignedGraphEnergy_eq_gauged (m : Nat) (x : SGVertex m → ℝ) :
    sgSignedGraphEnergy m x =
      faceGraphEnergy (fun v => sgVertexGauge v * x v)
        (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
  classical
  unfold sgSignedGraphEnergy faceGraphEnergy
  apply Finset.sum_congr rfl
  intro e he
  exact sgSignedEdgeTerm_eq_gauge x e.1 e.2

/-- Uniform signed energy lower bound on every recursively defined gasket.
This is the quadratic-form statement corresponding to a spectral gap at
least one for the local-face signing. -/
theorem sgSignedGraphEnergy_lower_bound (m : Nat) (x : SGVertex m → ℝ) :
    (∑ v : SGVertex m, (x v) ^ 2) ≤ sgSignedGraphEnergy m x := by
  classical
  have hmass :
      (∑ v : SGVertex m, (x v) ^ 2) =
        ∑ v : SGVertex m, (sgVertexGauge v * x v) ^ 2 := by
    apply Finset.sum_congr rfl
    intro v hv
    calc
      (x v) ^ 2 = (sgVertexGauge v) ^ 2 * (x v) ^ 2 := by
        rw [sgVertexGauge_sq]
        ring
      _ = (sgVertexGauge v * x v) ^ 2 := by rw [mul_pow]
  calc
    (∑ v : SGVertex m, (x v) ^ 2) =
        ∑ v : SGVertex m, (sgVertexGauge v * x v) ^ 2 := hmass
    _ ≤ faceGraphEnergy (fun v => sgVertexGauge v * x v)
          (sgFaceA m) (sgFaceB m) (sgFaceC m) :=
      sg_graph_energy_lower_bound m (fun v => sgVertexGauge v * x v)
    _ = sgSignedGraphEnergy m x := (sgSignedGraphEnergy_eq_gauged m x).symm

end PhiGenesis.SpectralGap
