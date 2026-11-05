import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexStateA

open scoped List

namespace PhiGenesis.H10

/-- State-A point list of the cell with side `2 * 2^n` at the origin. -/
def stateAList (n : Nat) : List (Nat × Nat) :=
  [(0, 0), (gasketScale n, 0), (0, gasketScale n),
    (gasketScale n + gasketScale n, 0), (gasketScale n, gasketScale n),
    (0, gasketScale n + gasketScale n)]

/-- The same six points under an embedding `g`, in state-B order
q0, q1, h01, h02, h12, q2. -/
def cellOrderB (g : Nat × Nat → Nat × Nat) (S : Nat) : List (Nat × Nat) :=
  [g (0, 0), g (S + S, 0), g (S, 0), g (0, S), g (S, S), g (0, S + S)]

theorem stateAList_sublist (n : Nat) :
    stateAList n <+ gasketVertexOrder (n + 1) :=
  gasketVertexOrder_stateA n

/-- Child 0 of the level-(n+2) cell is in state A. -/
theorem gasketVertexOrder_child0_cellA (n : Nat) :
    (stateAList n).map (gasketChildPoint (n + 1) .corner0) <+
      gasketVertexOrder (n + 1 + 1) := by
  have h := (stateAList_sublist n).map (gasketChildPoint (n + 1) .corner0)
  exact h.trans (gasketVertexOrder_child0_prefix (n + 1)).sublist

/-- Child 1 of the level-(n+2) cell is in state A. -/
theorem gasketVertexOrder_child1_cellA (n : Nat) :
    (stateAList n).map (gasketChildPoint (n + 1) .corner1) <+
      gasketVertexOrder (n + 1 + 1) := by
  have hS : 0 < gasketScale n := by unfold gasketScale; positivity
  rcases gasketVertexOrder_outerCorners_mem (n + 1) with ⟨o0, o1, o2⟩
  have htail : (stateAList n).tail <+ gasketVertexOrder (n + 1) :=
    (List.tail_sublist _).trans (stateAList_sublist n)
  have hB1 : (stateAList n).tail.map (gasketChildPoint (n + 1) .corner1) <+
      (gasketVertexOrder (n + 1)).map (gasketChildPoint (n + 1) .corner1) :=
    htail.map _
  have hfil := sublist_filter_of_forall
    (fun y => y ≠ (gasketScale (n + 1), 0)) hB1 (by
      intro x hx
      simp [stateAList, gasketChildPoint, gasketScale_succ] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        simp [gasketScale_succ, Prod.ext_iff] <;> omega)
  have hsplit : (stateAList n).map (gasketChildPoint (n + 1) .corner1) =
      [gasketChildPoint (n + 1) .corner1 (0, 0)] ++
        (stateAList n).tail.map (gasketChildPoint (n + 1) .corner1) := rfl
  have hhead : gasketChildPoint (n + 1) .corner1 (0, 0) ∈
      (gasketVertexOrder (n + 1)).map (gasketChildPoint (n + 1) .corner0) := by
    rw [gasketVertexOrder_map_child0]
    have : gasketChildPoint (n + 1) .corner1 (0, 0) =
        gasketOuterCorner (n + 1) .corner1 := by
      simp [gasketChildPoint, gasketOuterCorner]
    rw [this]
    exact o1
  rw [hsplit, gasketVertexOrder_succ_explicit (n + 1)]
  exact List.Sublist.append (List.singleton_sublist.mpr hhead)
    (hfil.trans (List.sublist_append_left _ _))

/-- Child 2 of the level-(n+2) cell is in state B. -/
theorem gasketVertexOrder_child2_cellB (n : Nat) :
    cellOrderB (gasketChildPoint (n + 1) .corner2) (gasketScale n) <+
      gasketVertexOrder (n + 1 + 1) := by
  have hS : 0 < gasketScale n := by unfold gasketScale; positivity
  rcases gasketVertexOrder_outerCorners_mem (n + 1) with ⟨o0, o1, o2⟩
  have hA := stateAList_sublist n
  have hpick : [((gasketScale n, 0) : Nat × Nat), (0, gasketScale n),
      (gasketScale n, gasketScale n),
      (0, gasketScale n + gasketScale n)] <+ stateAList n :=
    List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _
      (List.Sublist.cons _ (List.Sublist.cons₂ _ (List.Sublist.cons₂ _
        List.Sublist.slnil)))))
  have hrest := (hpick.trans hA).map (gasketChildPoint (n + 1) .corner2)
  have hf1 := sublist_filter_of_forall
    (fun y => y ≠ (0, gasketScale (n + 1))) hrest (by
      intro x hx
      simp [gasketChildPoint, gasketScale_succ] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gasketScale_succ, Prod.ext_iff] <;> omega)
  have hf2 := sublist_filter_of_forall
    (fun y => y ≠ (gasketScale (n + 1), gasketScale (n + 1))) hf1 (by
      intro x hx
      simp [gasketChildPoint, gasketScale_succ] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [gasketScale_succ, Prod.ext_iff] <;> omega)
  have h0 : gasketChildPoint (n + 1) .corner2 (0, 0) ∈
      (gasketVertexOrder (n + 1)).map (gasketChildPoint (n + 1) .corner0) := by
    rw [gasketVertexOrder_map_child0]
    have : gasketChildPoint (n + 1) .corner2 (0, 0) =
        gasketOuterCorner (n + 1) .corner2 := by
      simp [gasketChildPoint, gasketOuterCorner]
    rw [this]
    exact o2
  have h3 : gasketChildPoint (n + 1) .corner2
        (gasketScale n + gasketScale n, 0) ∈
      ((gasketVertexOrder (n + 1)).map (gasketChildPoint (n + 1) .corner1)).filter
        (fun y => y ≠ (gasketScale (n + 1), 0)) := by
    refine List.mem_filter.mpr ⟨List.mem_map.mpr
      ⟨gasketOuterCorner (n + 1) .corner2, o2, ?_⟩, ?_⟩
    · simp [gasketChildPoint, gasketOuterCorner, gasketScale_succ]
    · simp [gasketChildPoint, gasketScale_succ, Prod.ext_iff] <;> omega
  unfold cellOrderB
  rw [gasketVertexOrder_succ_explicit (n + 1)]
  exact List.Sublist.append (List.singleton_sublist.mpr h0)
    (List.Sublist.append (List.singleton_sublist.mpr h3) hf2)



/-- The cell at address 21 realizes state C in the actual
first-occurrence vertex list. Its q₁ vertex is already present in the
root child-1 block; the other five points occur in the filtered root
child-2 block in the inherited state-A order. This is the first concrete
B-to-C transition, not merely an instance of the abstract automaton. -/
theorem gasketVertexOrder_child21_cellC (n : Nat) :
    [(gasketScale (n + 2), gasketScale (n + 2)),
      (gasketScale (n + 1), gasketScale (n + 2)),
      (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1) + gasketScale n,
        gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
        gasketVertexOrder (n + 3) := by
  have hR : 0 < gasketScale (n + 1) := by
    unfold gasketScale
    positivity
  have hT : 0 < gasketScale (n + 2) := by
    unfold gasketScale
    positivity
  let inner := gasketChildPoint (n + 1) .corner1
  let outer := gasketChildPoint (n + 2) .corner2
  let sourceMap := ((stateAList n).map inner).map outer
  let globalMap := (gasketVertexOrder (n + 2)).map outer
  have hMap : sourceMap <+ globalMap := by
    exact (gasketVertexOrder_child1_cellA n).map outer
  have hNoBottom : ∀ y ∈ sourceMap,
      decide (y ≠ (0, gasketScale (n + 2))) = true := by
    intro y hy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    rcases List.mem_map.mp hz with ⟨p, hp, rfl⟩
    apply decide_eq_true
    intro heq
    simp [inner, outer, gasketChildPoint] at heq
    omega
  have hFiltered0 :
      sourceMap <+ globalMap.filter
        (fun p => decide (p ≠ (0, gasketScale (n + 2)))) :=
    sublist_filter_of_forall _ hMap hNoBottom
  have hFiltered :
      sourceMap.filter
          (fun p => decide (p ≠
            (gasketScale (n + 2), gasketScale (n + 2))) <+
        (globalMap.filter
          (fun p => decide (p ≠ (0, gasketScale (n + 2)))).filter
          (fun p => decide (p ≠
            (gasketScale (n + 2), gasketScale (n + 2)))) :=
    hFiltered0.filter _
  have hSourceFilter :
      sourceMap.filter
          (fun p => decide (p ≠ (0, gasketScale (n + 2))) = true := by
    exact List.filter_eq_self.mpr hNoBottom
  have hTailEq :
      sourceMap.filter
          (fun p => decide (p ≠ (0, gasketScale (n + 2)))).filter
          (fun p => decide (p ≠
            (gasketScale (n + 2), gasketScale (n + 2))) =
        [(gasketScale (n + 1), gasketScale (n + 2)),
          (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
          (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
          (gasketScale (n + 1) + gasketScale n,
            gasketScale (n + 2) + gasketScale n),
          (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] := by
    simp [sourceMap, inner, outer, stateAList, gasketChildPoint,
      gasketScale_succ, Prod.ext_iff] <;> omega
  have hTail :
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      (globalMap.filter
        (fun p => decide (p ≠ (0, gasketScale (n + 2)))).filter
        (fun p => decide (p ≠
          (gasketScale (n + 2), gasketScale (n + 2)))) := by
    rw [← hTailEq]
    rw [hSourceFilter]
    exact hFiltered
  rcases gasketVertexOrder_outerCorners_mem (n + 2) with ⟨_, _, hcorner2⟩
  have hq1 : (gasketScale (n + 2), gasketScale (n + 2)) ∈
      ((gasketVertexOrder (n + 2)).map
        (gasketChildPoint (n + 2) .corner1)).filter
        (fun p => p ≠ (gasketScale (n + 2), 0)) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_map.mpr
      ⟨(0, gasketScale (n + 2)), hcorner2, ?_⟩, ?_⟩
    · simp [gasketChildPoint]
    · exact decide_eq_true (by
        intro heq
        have hsecond := congrArg Prod.snd heq
        simp at hsecond
        omega)
  have hPair :
      [(gasketScale (n + 2), gasketScale (n + 2))] ++
          [(gasketScale (n + 1), gasketScale (n + 2)),
            (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
            (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
            (gasketScale (n + 1) + gasketScale n,
              gasketScale (n + 2) + gasketScale n),
            (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
        ((gasketVertexOrder (n + 2)).map
          (gasketChildPoint (n + 2) .corner1)).filter
          (fun p => p ≠ (gasketScale (n + 2), 0)) ++
        ((gasketVertexOrder (n + 2)).map
          (gasketChildPoint (n + 2) .corner2)).filter
          (fun p => p ≠ (0, gasketScale (n + 2))).filter
          (fun p => p ≠
            (gasketScale (n + 2), gasketScale (n + 2))) :=
    List.Sublist.append (List.singleton_sublist.mpr hq1) hTail
  rw [gasketVertexOrder_succ_explicit (n + 2)]
  simpa using
    (List.Sublist.append (List.Sublist.slnil) hPair)

end PhiGenesis.H10
