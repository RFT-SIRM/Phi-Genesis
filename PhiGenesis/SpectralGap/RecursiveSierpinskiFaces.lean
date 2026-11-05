import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.FiniteFaceCover

/-!
# Recursive Sierpinski face addresses

An address of length `m` selects one of the three corner subgaskets at
each scale. The leading digit chooses the translate by `0`, `(2^m,0)`,
or `(0,2^m)`. Face corners are represented in integer triangular-lattice
coordinates. The vertex type is the finite image of all face-corner slots.
-/

namespace PhiGenesis.SpectralGap

/-- Translation selected by the leading address digit. -/
def sgChildOffset (m : Nat) (child : Fin 3) : Nat × Nat :=
  if child = 1 then (2 ^ m, 0) else if child = 2 then (0, 2 ^ m) else (0, 0)

/-- Add one recursive child translation to a face origin. -/
def sgAddOffset (m : Nat) (child : Fin 3) (p : Nat × Nat) : Nat × Nat :=
  (p.1 + (sgChildOffset m child).1, p.2 + (sgChildOffset m child).2)

/-- Remove the leading address digit. -/
def sgFaceTail {m : Nat} (w : Fin (m + 1) → Fin 3) : Fin m → Fin 3 :=
  fun i => w i.succ

/-- The integer-lattice origin of a face address.
The leading digit is the coarsest recursive child; the tail determines
the position inside that child copy. -/
def sgFaceOrigin : (m : Nat) → (Fin m → Fin 3) → Nat × Nat
  | 0, _ => (0, 0)
  | m + 1, w => sgAddOffset m (w 0) (sgFaceOrigin m (sgFaceTail w))

/-- A child translate sends a level-`m` origin into the level-`m+1` box. -/
theorem sgAddOffset_bounds (m : Nat) (child : Fin 3) (p : Nat × Nat)
    (hp : p.1 < 2 ^ m ∧ p.2 < 2 ^ m) :
    (sgAddOffset m child p).1 < 2 ^ (m + 1) ∧
      (sgAddOffset m child p).2 < 2 ^ (m + 1) := by
  rcases hp with ⟨hpx, hpy⟩
  have hpow : 2 ^ (m + 1) = 2 ^ m * 2 := by rw [pow_succ]
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) _
  fin_cases child <;>
    simp [sgAddOffset, sgChildOffset] <;> omega

/-- Within one child copy, the translate uniquely determines both the
child digit and the old origin, because the three translated boxes are
pairwise disjoint. -/
theorem sgAddOffset_injective_on_box (m : Nat)
    (c d : Fin 3) (p q : Nat × Nat)
    (hp : p.1 < 2 ^ m ∧ p.2 < 2 ^ m)
    (hq : q.1 < 2 ^ m ∧ q.2 < 2 ^ m)
    (h : sgAddOffset m c p = sgAddOffset m d q) :
    c = d ∧ p = q := by
  rcases hp with ⟨hpx, hpy⟩
  rcases hq with ⟨hqx, hqy⟩
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) _
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  fin_cases c <;> fin_cases d <;>
    simp [sgAddOffset, sgChildOffset] at hx hy ⊢ <;>
    first
    | apply Prod.ext <;> omega
    | omega

/-- Every level-`m` face origin lies in the half-open square of side `2^m`. -/
theorem sgFaceOrigin_bounds : ∀ m (w : Fin m → Fin 3),
    (sgFaceOrigin m w).1 < 2 ^ m ∧ (sgFaceOrigin m w).2 < 2 ^ m
  | 0, _ => by simp [sgFaceOrigin]
  | m + 1, w => by
      simpa [sgFaceOrigin] using
        sgAddOffset_bounds m (w 0) (sgFaceOrigin m (sgFaceTail w))
          (sgFaceOrigin_bounds m (sgFaceTail w))

/-- The recursive address-to-origin map is injective. -/
theorem sgFaceOrigin_injective : ∀ m, Function.Injective (sgFaceOrigin m)
  | 0 => by
      intro w z h
      funext i
      exact Fin.elim0 i
  | m + 1 => by
      intro w z h
      have hw := sgFaceOrigin_bounds m (sgFaceTail w)
      have hz := sgFaceOrigin_bounds m (sgFaceTail z)
      have hoff :
          sgAddOffset m (w 0) (sgFaceOrigin m (sgFaceTail w)) =
            sgAddOffset m (z 0) (sgFaceOrigin m (sgFaceTail z)) := by
        simpa [sgFaceOrigin] using h
      rcases sgAddOffset_injective_on_box m (w 0) (z 0)
          (sgFaceOrigin m (sgFaceTail w))
          (sgFaceOrigin m (sgFaceTail z)) hw hz hoff with
        ⟨hhead, htailOrigin⟩
      have htail : sgFaceTail w = sgFaceTail z :=
        sgFaceOrigin_injective m htailOrigin
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hhead
      · exact congrFun htail j

/-- Coordinates of the three corners of a recursively addressed face. -/
def sgFaceCornerCoords (m : Nat) :
    (Fin m → Fin 3) × TriangleCorner → Nat × Nat
  | (f, .leftBase) => sgFaceOrigin m f
  | (f, .rightBase) => ((sgFaceOrigin m f).1 + 1, (sgFaceOrigin m f).2)
  | (f, .apex) => ((sgFaceOrigin m f).1, (sgFaceOrigin m f).2 + 1)

/-- The finite set of all vertices appearing as corners of level-`m` faces. -/
def sgVertexFinset (m : Nat) : Finset (Nat × Nat) :=
  Finset.univ.image (sgFaceCornerCoords m)

/-- The actual level-`m` vertex type, represented by integer lattice coordinates. -/
def SGVertex (m : Nat) := {v : Nat × Nat // v ∈ sgVertexFinset m}

noncomputable instance sgVertexFintype (m : Nat) : Fintype (SGVertex m) :=
  Fintype.ofFinset (sgVertexFinset m) (by intro v; rfl)

noncomputable instance sgVertexDecidableEq (m : Nat) : DecidableEq (SGVertex m) :=
  Classical.decEq _

/-- A face-corner slot, viewed as a vertex of the finite gasket graph. -/
def sgCornerVertex (m : Nat)
    (p : (Fin m → Fin 3) × TriangleCorner) : SGVertex m :=
  ⟨sgFaceCornerCoords m p, by simp [sgVertexFinset]⟩

/-- Every level-`m` vertex is represented by at least one face-corner slot. -/
theorem sgCornerVertex_surjective (m : Nat) :
    Function.Surjective (sgCornerVertex m) := by
  intro v
  have hv : v.1 ∈ Finset.univ.image (sgFaceCornerCoords m) := by
    simpa [sgVertexFinset] using v.2
  rcases Finset.mem_image.mp hv with ⟨p, hp, hcoord⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  exact hcoord

/-- The three vertex maps of a face in the finite gasket graph. -/
def sgFaceA (m : Nat) (f : Fin m → Fin 3) : SGVertex m :=
  sgCornerVertex m (f, .leftBase)
def sgFaceB (m : Nat) (f : Fin m → Fin 3) : SGVertex m :=
  sgCornerVertex m (f, .rightBase)
def sgFaceC (m : Nat) (f : Fin m → Fin 3) : SGVertex m :=
  sgCornerVertex m (f, .apex)

/-- The generic face-corner map agrees with the concrete recursive vertices. -/
theorem sgFaceCornerMap_eq (m : Nat) :
    faceCornerVertex (sgFaceA m) (sgFaceB m) (sgFaceC m) = sgCornerVertex m := by
  funext p
  rcases p with ⟨f, corner⟩
  cases corner <;> rfl

/-- The concrete face-corner map covers every vertex of the level-`m` gasket. -/
theorem sgFaceCornerMap_surjective (m : Nat) :
    Function.Surjective (faceCornerVertex (sgFaceA m) (sgFaceB m) (sgFaceC m) :
      ((Fin m → Fin 3) × TriangleCorner) → SGVertex m) := by
  rw [sgFaceCornerMap_eq]
  exact sgCornerVertex_surjective m

/-- Ordered coordinate endpoints of a face-edge slot. -/
def sgFaceEdgeCoords (m : Nat) :
    ((Fin m → Fin 3) × TriangleEdge) → (Nat × Nat) × (Nat × Nat)
  | (f, .base) => (sgFaceCornerCoords m (f, .leftBase),
      sgFaceCornerCoords m (f, .rightBase))
  | (f, .left) => (sgFaceCornerCoords m (f, .leftBase),
      sgFaceCornerCoords m (f, .apex))
  | (f, .right) => (sgFaceCornerCoords m (f, .rightBase),
      sgFaceCornerCoords m (f, .apex))

/-- Equality of coordinate edge endpoints determines both the face address
and its edge direction. -/
theorem sgFaceEdgeCoords_injective (m : Nat) :
    Function.Injective (sgFaceEdgeCoords m) := by
  classical
  intro p q h
  rcases p with ⟨f, e⟩
  rcases q with ⟨g, e'⟩
  rcases Prod.mk.inj h with ⟨hStart, hEnd⟩
  rcases Prod.mk.inj hStart with ⟨h₁x, h₁y⟩
  rcases Prod.mk.inj hEnd with ⟨h₂x, h₂y⟩
  fin_cases e <;> fin_cases e'
  all_goals simp [sgFaceCornerCoords] at h₁x h₁y h₂x h₂y
  all_goals
    first
    | have hOrigin : sgFaceOrigin m f = sgFaceOrigin m g := by
        apply Prod.ext <;> omega
      have hfg : f = g := sgFaceOrigin_injective m hOrigin
      subst g
      rfl
    | omega

/-- The coordinate edge map is exactly the subtype-value projection of the
actual graph edge-slot map. -/
theorem sgFaceEdgeCoords_eq_val (m : Nat)
    (p : (Fin m → Fin 3) × TriangleEdge) :
    sgFaceEdgeCoords m p =
      ((faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1.1,
       (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2.1) := by
  rcases p with ⟨f, edge⟩
  cases edge <;> rfl

/-- No two face-edge slots in the recursive gasket describe the same
ordered endpoint pair. -/
theorem sgFaceEdgeEndpoints_injective (m : Nat) :
    Function.Injective (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m)) := by
  intro p q h
  have hval := congrArg
    (fun z : SGVertex m × SGVertex m => (z.1.1, z.2.1)) h
  rw [← sgFaceEdgeCoords_eq_val m p, ← sgFaceEdgeCoords_eq_val m q] at hval
  exact sgFaceEdgeCoords_injective m hval

/-- The global energy lower bound now applies to every recursively defined
Sierpinski level: face edges are not repeated and all vertices are covered. -/
theorem sg_graph_energy_lower_bound (m : Nat) (x : SGVertex m → ℝ) :
    (∑ v : SGVertex m, (x v) ^ 2) ≤
      faceGraphEnergy x (sgFaceA m) (sgFaceB m) (sgFaceC m) := by
  classical
  exact faceGraphEnergy_lower_bound_of_surjective_corners
    x (sgFaceA m) (sgFaceB m) (sgFaceC m)
    (sgFaceEdgeEndpoints_injective m) (sgFaceCornerMap_surjective m)

end PhiGenesis.SpectralGap
