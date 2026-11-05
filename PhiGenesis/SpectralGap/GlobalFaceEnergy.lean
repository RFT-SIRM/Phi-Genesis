import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.TriangleEnergy

/-!
# Global face-energy estimate

This file converts the local triangle inequality into a global lower bound
for any finite triangular face decomposition with disjoint edge indexing
and an injective choice of one incident face-corner for every vertex.
The hypotheses are explicit: no multiplicity or coverage claim is hidden.
-/

namespace PhiGenesis.SpectralGap

/-- The three corners of a triangular face. -/
inductive TriangleCorner where
  | leftBase
  | rightBase
  | apex
  deriving DecidableEq, Fintype

/-- The three edge slots of a triangle, in its canonical face orientation. -/
inductive TriangleEdge where
  | base
  | left
  | right
  deriving DecidableEq, Fintype

/-- The vertex at a chosen corner of a face. -/
def faceCornerVertex {V F : Type*} (a b c : F → V) : F × TriangleCorner → V
  | (f, .leftBase) => a f
  | (f, .rightBase) => b f
  | (f, .apex) => c f

/-- The ordered endpoints of an edge slot in a face. -/
def faceEdgeEndpoints {V F : Type*} (a b c : F → V) : F × TriangleEdge → V × V
  | (f, .base) => (a f, b f)
  | (f, .left) => (a f, c f)
  | (f, .right) => (b f, c f)

/-- The squared vertex mass contributed by one face. -/
def faceCornerMass {V F : Type*} (x : V → ℝ) (a b c : F → V) (f : F) : ℝ :=
  (x (a f)) ^ 2 + (x (b f)) ^ 2 + (x (c f)) ^ 2

/-- The pair-energy contributed by the three edges of one face. -/
def facePairEnergy {V F : Type*} (x : V → ℝ) (a b c : F → V) (f : F) : ℝ :=
  (x (a f) + x (b f)) ^ 2 +
    (x (a f) + x (c f)) ^ 2 +
    (x (b f) + x (c f)) ^ 2

/-- The graph edge set obtained from all face-edge slots. -/
def faceGraphEdges {V F : Type*} [DecidableEq V] [Fintype F]
    (a b c : F → V) : Finset (V × V) :=
  Finset.univ.image (faceEdgeEndpoints a b c)

/-- The quadratic energy on the graph edge set, counted once per edge. -/
def faceGraphEnergy {V F : Type*} [DecidableEq V] [Fintype F]
    (x : V → ℝ) (a b c : F → V) : ℝ :=
  ∑ e ∈ faceGraphEdges a b c, (x e.1 + x e.2) ^ 2

/-- Summing face-corner mass is the same as summing over all corner slots. -/
theorem sum_faceCornerMass_eq_cornerSlots
    {V F : Type*} [Fintype F]
    (x : V → ℝ) (a b c : F → V) :
    (∑ f : F, faceCornerMass x a b c f) =
      ∑ p : F × TriangleCorner, (x (faceCornerVertex a b c p)) ^ 2 := by
  simp [faceCornerMass, faceCornerVertex, Fintype.sum_prod_type]

/-- Summing one-face pair energies is the same as summing over all edge slots. -/
theorem sum_facePairEnergy_eq_edgeSlots
    {V F : Type*} [Fintype F]
    (x : V → ℝ) (a b c : F → V) :
    (∑ f : F, facePairEnergy x a b c f) =
      ∑ p : F × TriangleEdge,
        (x (faceEdgeEndpoints a b c p).1 + x (faceEdgeEndpoints a b c p).2) ^ 2 := by
  simp [facePairEnergy, faceEdgeEndpoints, Fintype.sum_prod_type]

/-- Every face contributes at least the squared mass of its three corners. -/
theorem faceCornerMass_le_pairEnergy
    {V F : Type*} (x : V → ℝ) (a b c : F → V) (f : F) :
    faceCornerMass x a b c f ≤ facePairEnergy x a b c f := by
  exact trianglePairEnergy_lower_bound (x (a f)) (x (b f)) (x (c f))

/-- The sum over an injectively selected subset of nonnegative terms is bounded
by the sum over the full finite index type. -/
theorem sum_image_nonneg_le_univ
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (e : α ↪ β) (g : β → ℝ) (hg : ∀ b, 0 ≤ g b) :
    (∑ b ∈ Finset.univ.image e, g b) ≤ ∑ b : β, g b := by
  classical
  let s : Finset β := Finset.univ.image e
  have hdisj : Disjoint s (Finset.univ \ s) := by
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    exact (Finset.mem_sdiff.mp hb').2 hb
  have hunion : s ∪ (Finset.univ \ s) = Finset.univ := by
    ext b
    simp [s]
  have hrest : 0 ≤ ∑ b ∈ Finset.univ \ s, g b :=
    Finset.sum_nonneg fun b hb => hg b
  calc
    (∑ b ∈ Finset.univ.image e, g b) = ∑ b ∈ s, g b := by simp [s]
    _ ≤ (∑ b ∈ s, g b) + ∑ b ∈ Finset.univ \ s, g b :=
      le_add_of_nonneg_right hrest
    _ = ∑ b : β, g b := by
      rw [← Finset.sum_union hdisj, hunion]
      simp

/-- Vertex mass is bounded by total face-corner mass whenever each vertex
has a distinct chosen corner in the face family. -/
theorem vertexMass_le_totalCornerMass
    {V F : Type*} [Fintype V] [Fintype F] [DecidableEq F]
    (x : V → ℝ) (a b c : F → V)
    (cover : V ↪ F × TriangleCorner)
    (hCover : ∀ v, faceCornerVertex a b c (cover v) = v) :
    (∑ v : V, (x v) ^ 2) ≤
      ∑ p : F × TriangleCorner, (x (faceCornerVertex a b c p)) ^ 2 := by
  classical
  let selected : Finset (F × TriangleCorner) := Finset.univ.image cover
  have hImage :
      (∑ p ∈ selected, (x (faceCornerVertex a b c p)) ^ 2) =
        ∑ v : V, (x v) ^ 2 := by
    dsimp [selected]
    have hinj : Set.InjOn (fun v : V => cover v) (↑(Finset.univ : Finset V)) := by
      intro v hv w hw h
      exact cover.injective h
    rw [Finset.sum_image hinj]
    simp [hCover]
  have hSubset := sum_image_nonneg_le_univ cover
    (fun p => (x (faceCornerVertex a b c p)) ^ 2)
    (fun p => sq_nonneg (x (faceCornerVertex a b c p)))
  calc
    (∑ v : V, (x v) ^ 2) =
        ∑ p ∈ selected, (x (faceCornerVertex a b c p)) ^ 2 := hImage.symm
    _ ≤ ∑ p : F × TriangleCorner, (x (faceCornerVertex a b c p)) ^ 2 := by
      simpa [selected] using hSubset

/-- Global face-energy inequality: the graph energy controls the vertex norm.
The edge-injectivity hypothesis says that no geometric edge is counted twice
by the face decomposition. The corner embedding chooses one incident face
corner for every vertex, so vertices are not lost in the lower estimate. -/
theorem faceGraphEnergy_lower_bound
    {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (x : V → ℝ) (a b c : F → V)
    (hEdges : Function.Injective (faceEdgeEndpoints a b c))
    (cover : V ↪ F × TriangleCorner)
    (hCover : ∀ v, faceCornerVertex a b c (cover v) = v) :
    (∑ v : V, (x v) ^ 2) ≤ faceGraphEnergy x a b c := by
  classical
  have hCoverMass :
      (∑ v : V, (x v) ^ 2) ≤ ∑ f : F, faceCornerMass x a b c f := by
    calc
      (∑ v : V, (x v) ^ 2) ≤
          ∑ p : F × TriangleCorner, (x (faceCornerVertex a b c p)) ^ 2 :=
        vertexMass_le_totalCornerMass x a b c cover hCover
      _ = ∑ f : F, faceCornerMass x a b c f :=
        (sum_faceCornerMass_eq_cornerSlots x a b c).symm
  have hLocal :
      (∑ f : F, faceCornerMass x a b c f) ≤
        ∑ f : F, facePairEnergy x a b c f := by
    apply Finset.sum_le_sum
    intro f hf
    exact faceCornerMass_le_pairEnergy x a b c f
  have hEdgesEnergy :
      (∑ f : F, facePairEnergy x a b c f) = faceGraphEnergy x a b c := by
    unfold faceGraphEnergy faceGraphEdges
    calc
      (∑ f : F, facePairEnergy x a b c f) =
          ∑ p : F × TriangleEdge,
            (x (faceEdgeEndpoints a b c p).1 +
              x (faceEdgeEndpoints a b c p).2) ^ 2 :=
        sum_facePairEnergy_eq_edgeSlots x a b c
      _ = ∑ e ∈ Finset.univ.image (faceEdgeEndpoints a b c),
            (x e.1 + x e.2) ^ 2 := by
        symm
        have hinj :
            Set.InjOn (faceEdgeEndpoints a b c)
              (↑(Finset.univ : Finset (F × TriangleEdge))) := by
          intro p hp q hq hpq
          exact hEdges hpq
        rw [Finset.sum_image hinj]
        simp
  exact le_trans hCoverMass (hLocal.trans_eq hEdgesEnergy)

end PhiGenesis.SpectralGap
