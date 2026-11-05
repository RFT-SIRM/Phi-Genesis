import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexExplicit

open scoped List

namespace PhiGenesis.H10

variable {α : Type*}

theorem sublist_filter_of_forall {l1 l2 : List α} (p : α → Bool)
    (h : l1 <+ l2) (hp : ∀ x ∈ l1, p x = true) : l1 <+ l2.filter p := by
  have h2 := h.filter p
  rwa [List.filter_eq_self.mpr hp] at h2

theorem gasketVertexOrder_map_child0 (n : Nat) :
    (gasketVertexOrder n).map (gasketChildPoint n .corner0) =
      gasketVertexOrder n := by
  have h : (gasketVertexOrder n).map (gasketChildPoint n .corner0) =
      (gasketVertexOrder n).map id :=
    List.map_congr_left (fun p _ => rfl)
  rw [h, List.map_id]

/-- If the three outer corners appear in order at level n, then the six
distinguished points of the level-(n+1) cell appear in state-A order. -/
theorem gasketVertexOrder_stateA_of_corners (n : Nat)
    (hc : [gasketOuterCorner n .corner0, gasketOuterCorner n .corner1,
        gasketOuterCorner n .corner2] <+ gasketVertexOrder n) :
    [((0 : Nat), (0 : Nat)), (gasketScale n, 0), (0, gasketScale n),
      (gasketScale n + gasketScale n, 0), (gasketScale n, gasketScale n),
      (0, gasketScale n + gasketScale n)] <+ gasketVertexOrder (n + 1) := by
  have hS : 0 < gasketScale n := by unfold gasketScale; positivity
  rcases gasketVertexOrder_outerCorners_mem n with ⟨o0, o1, o2⟩
  rw [gasketVertexOrder_succ_explicit]
  have hB0 : [((0 : Nat), (0 : Nat)), (gasketScale n, 0), (0, gasketScale n)] <+
      (gasketVertexOrder n).map (gasketChildPoint n .corner0) := by
    rw [gasketVertexOrder_map_child0]
    exact hc
  have htail : [gasketOuterCorner n .corner1, gasketOuterCorner n .corner2] <+
      gasketVertexOrder n :=
    List.Sublist.trans (List.Sublist.cons _ (List.Sublist.refl _)) hc
  have hm : [(gasketScale n + gasketScale n, 0),
        (0 + gasketScale n, gasketScale n)] <+
      (gasketVertexOrder n).map (gasketChildPoint n .corner1) :=
    htail.map (gasketChildPoint n .corner1)
  rw [Nat.zero_add] at hm
  have hne1 : ((gasketScale n + gasketScale n, 0) : Nat × Nat) ≠
      (gasketScale n, 0) := by
    intro h
    have h1 : gasketScale n + gasketScale n = gasketScale n :=
      congrArg Prod.fst h
    omega
  have hne2 : ((gasketScale n, gasketScale n) : Nat × Nat) ≠
      (gasketScale n, 0) := by
    intro h
    have h1 : gasketScale n = 0 := congrArg Prod.snd h
    omega
  have hT1 : [(gasketScale n + gasketScale n, 0), (gasketScale n, gasketScale n)] <+
      ((gasketVertexOrder n).map (gasketChildPoint n .corner1)).filter
        (fun y => y ≠ (gasketScale n, 0)) := by
    apply sublist_filter_of_forall _ hm
    intro y hy
    simp at hy
    rcases hy with rfl | rfl
    · exact decide_eq_true hne1
    · exact decide_eq_true hne2
  have hne3 : ((0, gasketScale n + gasketScale n) : Nat × Nat) ≠
      (0, gasketScale n) := by
    intro h
    have h1 : gasketScale n + gasketScale n = gasketScale n :=
      congrArg Prod.snd h
    omega
  have hne4 : ((0, gasketScale n + gasketScale n) : Nat × Nat) ≠
      (gasketScale n, gasketScale n) := by
    intro h
    have h1 : (0 : Nat) = gasketScale n := congrArg Prod.fst h
    omega
  have hmem2 : ((0 : Nat), gasketScale n + gasketScale n) ∈
      (gasketVertexOrder n).map (gasketChildPoint n .corner2) :=
    List.mem_map.mpr ⟨gasketOuterCorner n .corner2, o2, rfl⟩
  have hT2 : [((0 : Nat), gasketScale n + gasketScale n)] <+
      (((gasketVertexOrder n).map (gasketChildPoint n .corner2)).filter
        (fun y => y ≠ (0, gasketScale n))).filter
        (fun y => y ≠ (gasketScale n, gasketScale n)) :=
    List.singleton_sublist.mpr
      (List.mem_filter.mpr
        ⟨List.mem_filter.mpr ⟨hmem2, decide_eq_true hne3⟩,
          decide_eq_true hne4⟩)
  exact List.Sublist.append hB0 (List.Sublist.append hT1 hT2)

/-- The three outer corners appear in the order q0, q1, q2 at every level. -/
theorem gasketVertexOrder_corners_sublist (n : Nat) :
    [gasketOuterCorner n .corner0, gasketOuterCorner n .corner1,
      gasketOuterCorner n .corner2] <+ gasketVertexOrder n := by
  induction n with
  | zero =>
      first
        | (rw [gasketVertexOrder_zero]; exact List.Sublist.refl _)
        | rw [gasketVertexOrder_zero]
  | succ n ih =>
      have hA := gasketVertexOrder_stateA_of_corners n ih
      have hpick : [((0 : Nat), (0 : Nat)),
            (gasketScale n + gasketScale n, 0),
            (0, gasketScale n + gasketScale n)] <+
          [((0 : Nat), (0 : Nat)), (gasketScale n, 0), (0, gasketScale n),
            (gasketScale n + gasketScale n, 0), (gasketScale n, gasketScale n),
            (0, gasketScale n + gasketScale n)] :=
        List.Sublist.cons₂ _ (List.Sublist.cons _ (List.Sublist.cons _
          (List.Sublist.cons₂ _ (List.Sublist.cons _
            (List.Sublist.cons₂ _ List.Sublist.slnil)))))
      have h := hpick.trans hA
      show [((0 : Nat), (0 : Nat)), (gasketScale (n + 1), 0),
        (0, gasketScale (n + 1))] <+ _
      rw [gasketScale_succ]
      exact h

/-- State A of the checkpoint table: at every level n+1 the six corner and
midpoint vertices of the whole cell occur in the order
q0, h01, h02, q1, h12, q2. -/
theorem gasketVertexOrder_stateA (n : Nat) :
    [((0 : Nat), (0 : Nat)), (gasketScale n, 0), (0, gasketScale n),
      (gasketScale n + gasketScale n, 0), (gasketScale n, gasketScale n),
      (0, gasketScale n + gasketScale n)] <+ gasketVertexOrder (n + 1) :=
  gasketVertexOrder_stateA_of_corners n (gasketVertexOrder_corners_sublist n)

end PhiGenesis.H10
