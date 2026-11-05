import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexOrder

/-!
# Geometric gluing of the recursively enumerated vertex sets

The global vertex order is obtained by first-occurrence deduplication of the
three child lists.  This file proves that all generated vertices lie in the
parent triangle and that each pair of child vertex sets meets in exactly
its prescribed shared midpoint.  These are the set-theoretic gluing facts
needed before deriving the six local A/B/C first-occurrence positions.
-/

namespace PhiGenesis.H10

/-- Every vertex in the recursively generated list lies in its level triangle. -/
theorem gasketVertexOrder_mem_triangle (n : Nat) :
    ∀ {p : GasketLatticePoint},
      p ∈ gasketVertexOrder n → gasketLatticeTriangle n p := by
  induction n with
  | zero =>
      intro p hp
      simp only [gasketVertexOrder, List.mem_cons] at hp
      rcases hp with h | h | h | h
      · subst p
        norm_num [gasketLatticeTriangle, gasketScale]
      · subst p
        norm_num [gasketLatticeTriangle, gasketScale]
      · subst p
        norm_num [gasketLatticeTriangle, gasketScale]
      · cases h
  | succ n ih =>
      intro p hp
      change p ∈ gasketFirstOccurrences
        ((gasketVertexOrder n).map (gasketChildPoint n .corner0) ++
          ((gasketVertexOrder n).map (gasketChildPoint n .corner1) ++
            (gasketVertexOrder n).map (gasketChildPoint n .corner2))) at hp
      have hmem := (gasketFirstOccurrences_mem_iff _ _).mp hp
      simp only [List.mem_append, List.mem_map] at hmem
      rcases hmem with h0 | h12
      · rcases h0 with ⟨q, hq, hEq⟩
        rw [← hEq]
        exact gasketChildPoint_preserves_triangle n .corner0 q (ih hq)
      · rcases h12 with h1 | h2
        · rcases h1 with ⟨q, hq, hEq⟩
          rw [← hEq]
          exact gasketChildPoint_preserves_triangle n .corner1 q (ih hq)
        · rcases h2 with ⟨q, hq, hEq⟩
          rw [← hEq]
          exact gasketChildPoint_preserves_triangle n .corner2 q (ih hq)

/-- The vertex sets of child 0 and child 1 meet exactly at (2^n, 0). -/
theorem gasketVertexOrder_child01_intersection (n : Nat) :
    ∀ p : GasketLatticePoint,
      p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner0) →
      (p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner1) ↔
        p = (gasketScale n, 0)) := by
  intro p hp0
  constructor
  · intro hp1
    rcases List.mem_map.mp hp0 with ⟨a, ha, haEq⟩
    rcases List.mem_map.mp hp1 with ⟨b, hb, hbEq⟩
    have hAB : gasketChildPoint n .corner0 a =
        gasketChildPoint n .corner1 b := by
      calc
        gasketChildPoint n .corner0 a = p := haEq
        _ = gasketChildPoint n .corner1 b := hbEq.symm
    have hmid := gasketChildPoint_zero_one_intersection n a b
      (gasketVertexOrder_mem_triangle n ha)
      (gasketVertexOrder_mem_triangle n hb) hAB
    calc
      p = gasketChildPoint n .corner0 a := haEq.symm
      _ = (gasketScale n, 0) := hmid
  · intro hp
    rw [hp]
    rcases gasketVertexOrder_outerCorners_mem n with ⟨h0, h1, h2⟩
    exact List.mem_map.mpr
      ⟨gasketOuterCorner n .corner0, h0, by
        simp [gasketChildPoint, gasketOuterCorner]⟩

/-- The vertex sets of child 0 and child 2 meet exactly at (0, 2^n). -/
theorem gasketVertexOrder_child02_intersection (n : Nat) :
    ∀ p : GasketLatticePoint,
      p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner0) →
      (p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner2) ↔
        p = (0, gasketScale n)) := by
  intro p hp0
  constructor
  · intro hp2
    rcases List.mem_map.mp hp0 with ⟨a, ha, haEq⟩
    rcases List.mem_map.mp hp2 with ⟨b, hb, hbEq⟩
    have hAB : gasketChildPoint n .corner0 a =
        gasketChildPoint n .corner2 b := by
      calc
        gasketChildPoint n .corner0 a = p := haEq
        _ = gasketChildPoint n .corner2 b := hbEq.symm
    have hmid := gasketChildPoint_zero_two_intersection n a b
      (gasketVertexOrder_mem_triangle n ha)
      (gasketVertexOrder_mem_triangle n hb) hAB
    calc
      p = gasketChildPoint n .corner0 a := haEq.symm
      _ = (0, gasketScale n) := hmid
  · intro hp
    rw [hp]
    rcases gasketVertexOrder_outerCorners_mem n with ⟨h0, h1, h2⟩
    exact List.mem_map.mpr
      ⟨gasketOuterCorner n .corner0, h0, by
        simp [gasketChildPoint, gasketOuterCorner]⟩

/-- The vertex sets of child 1 and child 2 meet exactly at (2^n, 2^n). -/
theorem gasketVertexOrder_child12_intersection (n : Nat) :
    ∀ p : GasketLatticePoint,
      p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner1) →
      (p ∈ (gasketVertexOrder n).map (gasketChildPoint n .corner2) ↔
        p = (gasketScale n, gasketScale n)) := by
  intro p hp1
  constructor
  · intro hp2
    rcases List.mem_map.mp hp1 with ⟨a, ha, haEq⟩
    rcases List.mem_map.mp hp2 with ⟨b, hb, hbEq⟩
    have hAB : gasketChildPoint n .corner1 a =
        gasketChildPoint n .corner2 b := by
      calc
        gasketChildPoint n .corner1 a = p := haEq
        _ = gasketChildPoint n .corner2 b := hbEq.symm
    have hmid := gasketChildPoint_one_two_intersection n a b
      (gasketVertexOrder_mem_triangle n ha)
      (gasketVertexOrder_mem_triangle n hb) hAB
    calc
      p = gasketChildPoint n .corner1 a := haEq.symm
      _ = (gasketScale n, gasketScale n) := hmid
  · intro hp
    rw [hp]
    rcases gasketVertexOrder_outerCorners_mem n with ⟨h0, h1, h2⟩
    exact List.mem_map.mpr
      ⟨gasketOuterCorner n .corner1, h1, by
        simp [gasketChildPoint, gasketOuterCorner]⟩

end PhiGenesis.H10
