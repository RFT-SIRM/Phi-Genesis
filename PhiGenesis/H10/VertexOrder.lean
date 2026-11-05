import Mathlib.Tactic

/-!
# The A/B/C corner-order automaton

This file formalizes the finite state data recorded in the H10 geometric
checkpoint.  The six symbols are the three cell corners and the three
edge midpoints.  A state records their first-occurrence order.  Address
digits update the state by the recursive A/B/C transition table.

The definitions below are the abstract finite automaton.  They do not,
by themselves, identify these symbols with the concrete first-occurrence
vertex IDs of the Python graph builder; that geometric realization is a
separate obligation.
-/

namespace PhiGenesis.H10

/-- The three possible first-occurrence states of a Sierpiński cell. -/
inductive GasketCornerOrderState where
  | A
  | B
  | C
  deriving DecidableEq, Repr

/-- The six distinguished vertices of a cell: its corners and side midpoints. -/
inductive GasketCornerVertex where
  | q0
  | q1
  | q2
  | h01
  | h02
  | h12
  deriving DecidableEq, Repr

/-- The six local vertices, listed in first-occurrence order in state A, B, or C. -/
def gasketCornerVertexOrder : GasketCornerOrderState → List GasketCornerVertex
  | .A => [.q0, .h01, .h02, .q1, .h12, .q2]
  | .B => [.q0, .q1, .h01, .h02, .h12, .q2]
  | .C => [.q1, .q0, .h01, .h02, .h12, .q2]

/-- The complete list of six distinguished cell vertices, without an order. -/
def gasketCornerVertexUniverse : List GasketCornerVertex :=
  [.q0, .q1, .q2, .h01, .h02, .h12]

/-- Passing to a child updates the corner-order state according to the
A/A/B and A/C/B transition rows from the geometric checkpoint. -/
def gasketCornerChildState
    (state : GasketCornerOrderState) (child : Fin 3) :
    GasketCornerOrderState :=
  if child.val = 0 then
    .A
  else if child.val = 1 then
    match state with
    | .A => .A
    | .B => .C
    | .C => .C
  else
    .B

/-- State of a cell addressed by a word of child digits, starting from root state A. -/
def gasketCornerOrderStateOfAddress
    (address : List (Fin 3)) : GasketCornerOrderState :=
  address.foldl gasketCornerChildState .A

@[simp] theorem gasketCornerChildState_zero
    (state : GasketCornerOrderState) :
    gasketCornerChildState state (0 : Fin 3) = .A := by
  simp [gasketCornerChildState]

@[simp] theorem gasketCornerChildState_two
    (state : GasketCornerOrderState) :
    gasketCornerChildState state (2 : Fin 3) = .B := by
  simp [gasketCornerChildState]

theorem gasketCornerChildState_one
    (state : GasketCornerOrderState) :
    gasketCornerChildState state (1 : Fin 3) =
      if state = .A then .A else .C := by
  cases state <;> rfl

/-- Appending one child digit applies exactly one transition to the state. -/
theorem gasketCornerOrderStateOfAddress_append
    (address : List (Fin 3)) (child : Fin 3) :
    gasketCornerOrderStateOfAddress (address ++ [child]) =
      gasketCornerChildState
        (gasketCornerOrderStateOfAddress address) child := by
  simp [gasketCornerOrderStateOfAddress, List.foldl_append]

@[simp] theorem gasketCornerOrderStateOfAddress_nil :
    gasketCornerOrderStateOfAddress [] = .A := rfl

/-- The child-state table holds uniformly at every address:
A has children A/A/B, while B and C have children A/C/B. -/
theorem gasketCornerOrderStateOfAddress_child_table
    (address : List (Fin 3)) :
    gasketCornerOrderStateOfAddress (address ++ [0]) = .A ∧
    gasketCornerOrderStateOfAddress (address ++ [1]) =
      (if gasketCornerOrderStateOfAddress address = .A then .A else .C) ∧
    gasketCornerOrderStateOfAddress (address ++ [2]) = .B := by
  have h0 := gasketCornerOrderStateOfAddress_append address (0 : Fin 3)
  have h1 := gasketCornerOrderStateOfAddress_append address (1 : Fin 3)
  have h2 := gasketCornerOrderStateOfAddress_append address (2 : Fin 3)
  rw [h0, h1, h2]
  cases gasketCornerOrderStateOfAddress address <;>
    simp [gasketCornerChildState]

/-- Each of the three states lists all six distinguished vertices exactly once. -/
theorem gasketCornerVertexOrder_perm_universe
    (state : GasketCornerOrderState) :
    List.Perm (gasketCornerVertexOrder state) gasketCornerVertexUniverse := by
  cases state <;> decide

/-- In every state the six-vertex order has no repetitions. -/
theorem gasketCornerVertexOrder_nodup
    (state : GasketCornerOrderState) :
    (gasketCornerVertexOrder state).Nodup := by
  cases state <;> decide

/-- The terminal corner q2 is last in all three order states. -/
theorem gasketCornerVertexOrder_q2_last
    (state : GasketCornerOrderState) :
    (gasketCornerVertexOrder state).getLast? = some .q2 := by
  cases state <;> rfl

end PhiGenesis.H10
