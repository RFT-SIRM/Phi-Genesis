import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import PhiGenesis.SpectralGap.GlobalFaceEnergy

/-!
# Finite corner covers and the base Sierpinski face

This module packages the finite choice of one corner slot per vertex.
It then checks the level-zero triangular graph as the first concrete
instance of the global face-energy inequality.
-/

namespace PhiGenesis.SpectralGap

/-- A surjective face-corner map admits an injective choice of one corner
slot for each vertex. The chosen slot is a right inverse of the corner map. -/
theorem cornerEmbedding_of_surjective
    {V F : Type*} (a b c : F → V)
    (hCorners : Function.Surjective (faceCornerVertex a b c)) :
    ∃ cover : V ↪ F × TriangleCorner,
      ∀ v, faceCornerVertex a b c (cover v) = v := by
  classical
  let chooseSlot : V → F × TriangleCorner := fun v => Classical.choose (hCorners v)
  have hChoose : ∀ v, faceCornerVertex a b c (chooseSlot v) = v := by
    intro v
    exact Classical.choose_spec (hCorners v)
  refine ⟨⟨chooseSlot, ?_⟩, hChoose⟩
  intro v w h
  calc
    v = faceCornerVertex a b c (chooseSlot v) := (hChoose v).symm
    _ = faceCornerVertex a b c (chooseSlot w) := congrArg (faceCornerVertex a b c) h
    _ = w := hChoose w

/-- Global face-energy estimate when every vertex occurs as a face corner.
The injective corner selector is constructed from surjectivity, rather than
being supplied as extra data. -/
theorem faceGraphEnergy_lower_bound_of_surjective_corners
    {V F : Type*} [Fintype V] [Fintype F] [DecidableEq V] [DecidableEq F]
    (x : V → ℝ) (a b c : F → V)
    (hEdges : Function.Injective (faceEdgeEndpoints a b c))
    (hCorners : Function.Surjective (faceCornerVertex a b c)) :
    (∑ v : V, (x v) ^ 2) ≤ faceGraphEnergy x a b c := by
  obtain ⟨cover, hCover⟩ := cornerEmbedding_of_surjective a b c hCorners
  exact faceGraphEnergy_lower_bound x a b c hEdges cover hCover

/-- The three vertices of the level-zero gasket. -/
def baseFaceA (_ : Unit) : Fin 3 := 0
def baseFaceB (_ : Unit) : Fin 3 := 1
def baseFaceC (_ : Unit) : Fin 3 := 2

/-- The three corner slots of the base face cover all three base vertices. -/
theorem baseFace_corners_surjective :
    Function.Surjective (faceCornerVertex baseFaceA baseFaceB baseFaceC) := by
  intro v
  fin_cases v
  · exact ⟨((), .leftBase), rfl⟩
  · exact ⟨((), .rightBase), rfl⟩
  · exact ⟨((), .apex), rfl⟩

/-- The three edge slots of the base triangle have distinct ordered endpoints. -/
theorem baseFace_edgeSlots_injective :
    Function.Injective (faceEdgeEndpoints baseFaceA baseFaceB baseFaceC) := by
  intro p q h
  rcases p with ⟨f, e⟩
  rcases q with ⟨g, e'⟩
  cases f
  cases g
  cases e <;> cases e' <;>
    simp [faceEdgeEndpoints, baseFaceA, baseFaceB, baseFaceC] at h ⊢

/-- The global energy inequality holds for the level-zero Sierpinski graph.
This is the first concrete instance; higher levels still require the recursive
face-family edge-disjointness and vertex-coverage proofs. -/
theorem baseFace_graph_energy_lower_bound (x : Fin 3 → ℝ) :
    (∑ v : Fin 3, (x v) ^ 2) ≤
      faceGraphEnergy x baseFaceA baseFaceB baseFaceC := by
  exact faceGraphEnergy_lower_bound_of_surjective_corners
    x baseFaceA baseFaceB baseFaceC
    baseFace_edgeSlots_injective baseFace_corners_surjective

end PhiGenesis.SpectralGap
