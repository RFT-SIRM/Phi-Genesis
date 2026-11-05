import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexOrder

namespace PhiGenesis.H10

/-- Exact membership description of the parent vertex list: a point is a
vertex of level `n+1` iff it is the image of a level-`n` vertex under one
of the three child embeddings. -/
theorem gasketVertexOrder_succ_mem_iff (n : Nat) (p : GasketLatticePoint) :
    p ∈ gasketVertexOrder (n + 1) ↔
      ∃ c : GasketChild, ∃ q ∈ gasketVertexOrder n,
        gasketChildPoint n c q = p := by
  change
    p ∈ gasketFirstOccurrences
      ((gasketVertexOrder n).map (gasketChildPoint n .corner0) ++
        ((gasketVertexOrder n).map (gasketChildPoint n .corner1) ++
          (gasketVertexOrder n).map (gasketChildPoint n .corner2))) ↔ _
  rw [gasketFirstOccurrences_mem_iff]
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨.corner0, q, hq, h⟩
    · exact ⟨.corner1, q, hq, h⟩
    · exact ⟨.corner2, q, hq, h⟩
  · rintro ⟨c, q, hq, h⟩
    cases c with
    | corner0 => exact Or.inl ⟨q, hq, h⟩
    | corner1 => exact Or.inr (Or.inl ⟨q, hq, h⟩)
    | corner2 => exact Or.inr (Or.inr ⟨q, hq, h⟩)

end PhiGenesis.H10
