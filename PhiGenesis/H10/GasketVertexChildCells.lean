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





/-- Exact coordinates of the six state-A points after entering child 1
of child 2. This is the geometric address-21 cell used in the concrete
state-C realization. The order here is still the inherited state-A order;
the later state-C permutation is caused by the earlier occurrence of
the cell's right-hand corner in the root child-1 block. -/
theorem stateAList_map_child21 (n : Nat) :
    ((stateAList n).map (gasketChildPoint (n + 1) .corner1)).map
        (gasketChildPoint (n + 2) .corner2) =
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 2), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] := by
  simp [stateAList, gasketChildPoint, gasketScale_succ,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]



/-- The q₁ point of the address-21 cell is already present in the
root child-1 block and survives that block's shared-midpoint filter.
This is the earlier occurrence responsible for the first entry of
the concrete state-C order. -/
theorem gasketVertexOrder_child21_q1_in_child1_block (n : Nat) :
    (gasketScale (n + 2), gasketScale (n + 2)) ∈
      ((gasketVertexOrder (n + 2)).map
        (gasketChildPoint (n + 2) .corner1)).filter
        (fun p => decide (p ≠ (gasketScale (n + 2), 0))) := by
  have hS : 0 < gasketScale (n + 2) := by
    unfold gasketScale
    positivity
  rcases gasketVertexOrder_outerCorners_mem (n + 2) with
    ⟨_, _, hcorner2⟩
  apply List.mem_filter.mpr
  refine ⟨List.mem_map.mpr
    ⟨(0, gasketScale (n + 2)), hcorner2, ?_⟩, ?_⟩
  · simp [gasketChildPoint]
  · exact decide_eq_true (by
      intro heq
      exact (Nat.ne_of_gt hS) (congrArg Prod.snd heq))


/-- The five address-21 points other than q₁ have first coordinate
strictly between the two possible shared-midpoint x-coordinates.
Consequently none can be removed by either root-child intersection
filter; the order/sublist argument is proved separately. -/
theorem gasketVertexOrder_child21_tail_x_between (n : Nat) :
    ∀ p ∈
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))],
      0 < p.1 ∧ p.1 < gasketScale (n + 2) := by
  have hS : 0 < gasketScale n := by
    unfold gasketScale
    positivity
  have hScale1 : gasketScale (n + 1) = 2 * gasketScale n := by
    rw [gasketScale_succ]
    omega
  have hScale2 : gasketScale (n + 2) = 4 * gasketScale n := by
    rw [show n + 2 = (n + 1) + 1 by omega, gasketScale_succ, hScale1]
    omega
  intro p hp
  simp only [List.mem_cons, List.mem_singleton] at hp
  rcases hp with h1 | h2 | h3 | h4 | h5
  · rw [h1]
    constructor <;> omega
  · rw [h2]
    constructor <;> omega
  · rw [h3]
    constructor <;> omega
  · rw [h4]
    constructor <;> omega
  · rcases h5 with h5 | hnil
    · rw [h5]
      constructor <;> omega
    · simp at hnil


/-- The five address-21 points other than q₁ occur, in their inherited
order, inside the root child-2 block after both shared-midpoint filters.
The omitted fourth point is q₁, whose earlier occurrence in child 1 is
handled by `gasketVertexOrder_child21_q1_in_child1_block`. -/
theorem gasketVertexOrder_child21_tail_sublist_child2_filtered (n : Nat) :
    [(gasketScale (n + 1), gasketScale (n + 2)),
      (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1) + gasketScale n,
        gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      (((gasketVertexOrder (n + 2)).map
          (gasketChildPoint (n + 2) .corner2)).filter
        (fun p => decide (p ≠ (0, gasketScale (n + 2))))).filter
        (fun p => decide
          (p ≠ (gasketScale (n + 2), gasketScale (n + 2)))) := by
  have hpick :
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 2), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] :=
    List.Sublist.cons_cons _ (List.Sublist.cons_cons _
      (List.Sublist.cons_cons _ (List.Sublist.cons _
        (List.Sublist.cons_cons _ (List.Sublist.cons_cons _
          List.Sublist.slnil)))))
  have hGlobal :
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 2), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      ((gasketVertexOrder (n + 2)).map
        (gasketChildPoint (n + 2) .corner2)) := by
    have h := (gasketVertexOrder_child1_cellA n).map
      (gasketChildPoint (n + 2) .corner2)
    rw [stateAList_map_child21 n] at h
    exact h
  have hTail := hpick.trans hGlobal
  have hLeft : ∀ p ∈
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))],
      decide (p ≠ (0, gasketScale (n + 2))) = true := by
    intro p hp
    rcases gasketVertexOrder_child21_tail_x_between n p hp with
      ⟨hpos, _⟩
    exact decide_eq_true (by
      intro heq
      have hfst : p.1 = 0 := congrArg Prod.fst heq
      omega)
  have hRight : ∀ p ∈
      [(gasketScale (n + 1), gasketScale (n + 2)),
        (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1) + gasketScale n,
          gasketScale (n + 2) + gasketScale n),
        (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))],
      decide (p ≠ (gasketScale (n + 2), gasketScale (n + 2))) = true := by
    intro p hp
    rcases gasketVertexOrder_child21_tail_x_between n p hp with
      ⟨_, hupper⟩
    exact decide_eq_true (by
      intro heq
      have hfst : p.1 = gasketScale (n + 2) := congrArg Prod.fst heq
      omega)
  have hFilter0 := sublist_filter_of_forall
    (fun p => decide (p ≠ (0, gasketScale (n + 2)))) hTail hLeft
  exact sublist_filter_of_forall
    (fun p => decide (p ≠ (gasketScale (n + 2), gasketScale (n + 2))))
    hFilter0 hRight


/-- The six distinguished vertices of the address-21 cell occur in
state-C order in the actual first-occurrence list of the level-(n+3)
gasket. The right corner occurs earlier in the root child-1 block;
the other five vertices occur, in order, in the filtered child-2 block. -/
theorem gasketVertexOrder_child21_cellC (n : Nat) :
    [(gasketScale (n + 2), gasketScale (n + 2)),
      (gasketScale (n + 1), gasketScale (n + 2)),
      (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1) + gasketScale n,
        gasketScale (n + 2) + gasketScale n),
      (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      gasketVertexOrder (n + 3) := by
  have hq1 := gasketVertexOrder_child21_q1_in_child1_block n
  have htail := gasketVertexOrder_child21_tail_sublist_child2_filtered n
  have hBlocks :
      [(gasketScale (n + 2), gasketScale (n + 2))] ++
        [(gasketScale (n + 1), gasketScale (n + 2)),
          (gasketScale (n + 1) + gasketScale n, gasketScale (n + 2)),
          (gasketScale (n + 1), gasketScale (n + 2) + gasketScale n),
          (gasketScale (n + 1) + gasketScale n,
            gasketScale (n + 2) + gasketScale n),
          (gasketScale (n + 1), gasketScale (n + 2) + gasketScale (n + 1))] <+
      (((gasketVertexOrder (n + 2)).map
          (gasketChildPoint (n + 2) .corner1)).filter
        (fun p => decide (p ≠ (gasketScale (n + 2), 0))) ++
        (((gasketVertexOrder (n + 2)).map
            (gasketChildPoint (n + 2) .corner2)).filter
          (fun p => decide (p ≠ (0, gasketScale (n + 2)))).filter
          (fun p => decide
            (p ≠ (gasketScale (n + 2), gasketScale (n + 2))))) := by
    exact List.Sublist.append (List.singleton_sublist.mpr hq1) htail
  rw [gasketVertexOrder_succ_explicit (n + 2)]
  exact List.sublist_append_of_sublist_right hBlocks

end PhiGenesis.H10
