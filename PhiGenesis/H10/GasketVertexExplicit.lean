import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexSplit
import PhiGenesis.H10.GasketVertexGeometry

namespace PhiGenesis.H10

variable {α : Type*}

theorem gasketFirstOccurrences_of_nodup [DecidableEq α] (xs : List α)
    (h : xs.Nodup) : gasketFirstOccurrences xs = xs := by
  have h2 := gasketFirstOccurrences_append_of_nodup xs [] h
  have h3 : gasketFirstOccurrences ([] : List α) = [] := by
    simp [gasketFirstOccurrences, gasketFirstOccurrencesAux]
  simpa [h3] using h2

theorem gasketFirstOccurrences_tail_explicit [DecidableEq α]
    (B0 B1 B2 : List α) (a b c : α)
    (hB1 : B1.Nodup) (hB2 : B2.Nodup)
    (h01 : ∀ p ∈ B0, (p ∈ B1 ↔ p = a))
    (h02 : ∀ p ∈ B0, (p ∈ B2 ↔ p = b))
    (h12 : ∀ p ∈ B1, (p ∈ B2 ↔ p = c))
    (ha : a ∈ B0) (hb : b ∈ B0) (hc : c ∈ B1) (hca : c ≠ a) :
    gasketFirstOccurrences ((B1 ++ B2).filter (fun y => y ∉ B0)) =
      B1.filter (fun y => y ≠ a) ++
        (B2.filter (fun y => y ≠ b)).filter (fun y => y ≠ c) := by
  have e1 : B1.filter (fun y => y ∉ B0) = B1.filter (fun y => y ≠ a) := by
    apply List.filter_congr
    intro y hy
    apply decide_eq_decide.mpr
    constructor
    · intro hn heq
      exact hn (by rw [heq]; exact ha)
    · intro hne hmem
      exact hne ((h01 y hmem).mp hy)
  have e2 : B2.filter (fun y => y ∉ B0) = B2.filter (fun y => y ≠ b) := by
    apply List.filter_congr
    intro y hy
    apply decide_eq_decide.mpr
    constructor
    · intro hn heq
      exact hn (by rw [heq]; exact hb)
    · intro hne hmem
      exact hne ((h02 y hmem).mp hy)
  have hB1' : (B1.filter (fun y => y ≠ a)).Nodup := hB1.filter _
  have hsplit := gasketFirstOccurrences_append_of_nodup
    (B1.filter (fun y => y ≠ a)) (B2.filter (fun y => y ≠ b)) hB1'
  have e3 :
      (B2.filter (fun y => y ≠ b)).filter
          (fun y => y ∉ B1.filter (fun y => y ≠ a)) =
        (B2.filter (fun y => y ≠ b)).filter (fun y => y ≠ c) := by
    apply List.filter_congr
    intro y hy
    have hy2 : y ∈ B2 := (List.mem_filter.mp hy).1
    apply decide_eq_decide.mpr
    constructor
    · intro hn heq
      apply hn
      rw [heq]
      exact List.mem_filter.mpr ⟨hc, by simpa using hca⟩
    · intro hne hmem
      exact hne ((h12 y (List.mem_filter.mp hmem).1).mp hy2)
  have hB2'' :
      ((B2.filter (fun y => y ≠ b)).filter (fun y => y ≠ c)).Nodup :=
    (hB2.filter _).filter _
  rw [List.filter_append, e1, e2, hsplit, e3,
    gasketFirstOccurrences_of_nodup _ hB2'']

theorem gasketVertexOrder_succ_explicit (n : Nat) :
    gasketVertexOrder (n + 1) =
      (gasketVertexOrder n).map (gasketChildPoint n .corner0) ++
        (((gasketVertexOrder n).map (gasketChildPoint n .corner1)).filter
            (fun y => y ≠ (gasketScale n, 0)) ++
          (((gasketVertexOrder n).map (gasketChildPoint n .corner2)).filter
              (fun y => y ≠ (0, gasketScale n))).filter
            (fun y => y ≠ (gasketScale n, gasketScale n))) := by
  have hS : 0 < gasketScale n := by unfold gasketScale; positivity
  rcases gasketVertexOrder_outerCorners_mem n with ⟨o0, o1, o2⟩
  have key := gasketFirstOccurrences_tail_explicit
    ((gasketVertexOrder n).map (gasketChildPoint n .corner0))
    ((gasketVertexOrder n).map (gasketChildPoint n .corner1))
    ((gasketVertexOrder n).map (gasketChildPoint n .corner2))
    (gasketScale n, 0) (0, gasketScale n) (gasketScale n, gasketScale n)
    ((gasketVertexOrder_nodup n).map (gasketChildPoint_injective n .corner1))
    ((gasketVertexOrder_nodup n).map (gasketChildPoint_injective n .corner2))
    (gasketVertexOrder_child01_intersection n)
    (gasketVertexOrder_child02_intersection n)
    (gasketVertexOrder_child12_intersection n)
    (List.mem_map.mpr ⟨gasketOuterCorner n .corner1, o1,
      by simp [gasketChildPoint, gasketOuterCorner]⟩)
    (List.mem_map.mpr ⟨gasketOuterCorner n .corner2, o2,
      by simp [gasketChildPoint, gasketOuterCorner]⟩)
    (List.mem_map.mpr ⟨gasketOuterCorner n .corner2, o2,
      by simp [gasketChildPoint, gasketOuterCorner]⟩)
    (by
      intro h
      have h2 : gasketScale n = 0 := congrArg Prod.snd h
      omega)
  rw [gasketVertexOrder_succ_eq_child0_append]
  congr 1
  convert key

end PhiGenesis.H10
