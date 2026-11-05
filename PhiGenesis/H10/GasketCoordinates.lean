import Mathlib.Tactic

/-!
# Exact integer geometry for recursive Sierpiński child embeddings

The Python graph builder contracts each child copy by one half and places
it at one of the three parent corners. In triangular-lattice coordinates,
scaled by 2^n at level n, these maps are exact integer translations.
This module formalizes the child geometry without floating point or rounding.

The first-occurrence vertex order and sorted primal-edge order remain
separate obligations; this module establishes their exact geometric input.
-/

namespace PhiGenesis.H10

abbrev GasketLatticePoint := Nat × Nat

inductive GasketChild where
  | corner0
  | corner1
  | corner2
  deriving DecidableEq, Repr

def gasketScale (n : Nat) : Nat := 2 ^ n

def gasketLatticeTriangle (n : Nat) (p : GasketLatticePoint) : Prop :=
  p.1 + p.2 ≤ gasketScale n

def gasketChildPoint (n : Nat) :
    GasketChild → GasketLatticePoint → GasketLatticePoint
  | .corner0, p => p
  | .corner1, p => (p.1 + gasketScale n, p.2)
  | .corner2, p => (p.1, p.2 + gasketScale n)

def gasketOuterCorner (n : Nat) : GasketChild → GasketLatticePoint
  | .corner0 => (0, 0)
  | .corner1 => (gasketScale n, 0)
  | .corner2 => (0, gasketScale n)

@[simp] theorem gasketScale_succ (n : Nat) :
    gasketScale (n + 1) = gasketScale n + gasketScale n := by
  simp only [gasketScale, pow_succ]
  omega

theorem gasketChildPoint_preserves_triangle
    (n : Nat) (c : GasketChild) (p : GasketLatticePoint)
    (hp : gasketLatticeTriangle n p) :
    gasketLatticeTriangle (n + 1) (gasketChildPoint n c p) := by
  cases c <;>
    simp [gasketLatticeTriangle, gasketChildPoint] at hp ⊢ <;>
    omega

theorem gasketChildPoint_injective (n : Nat) (c : GasketChild) :
    Function.Injective (gasketChildPoint n c) := by
  intro p q h
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  cases c <;> simp [gasketChildPoint] at h <;>
    apply Prod.ext <;> omega

theorem gasketChildPoint_zero_one_intersection
    (n : Nat) (p q : GasketLatticePoint)
    (hp : gasketLatticeTriangle n p) (hq : gasketLatticeTriangle n q)
    (h : gasketChildPoint n .corner0 p =
      gasketChildPoint n .corner1 q) :
    gasketChildPoint n .corner0 p = (gasketScale n, 0) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [gasketLatticeTriangle, gasketChildPoint] at hp hq h
  rcases h with ⟨hx, hy⟩
  have hpx : px = gasketScale n := by omega
  have hpy : py = 0 := by omega
  simp [gasketChildPoint, hpx, hpy]

theorem gasketChildPoint_zero_two_intersection
    (n : Nat) (p q : GasketLatticePoint)
    (hp : gasketLatticeTriangle n p) (hq : gasketLatticeTriangle n q)
    (h : gasketChildPoint n .corner0 p =
      gasketChildPoint n .corner2 q) :
    gasketChildPoint n .corner0 p = (0, gasketScale n) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [gasketLatticeTriangle, gasketChildPoint] at hp hq h
  rcases h with ⟨hx, hy⟩
  have hpx : px = 0 := by omega
  have hpy : py = gasketScale n := by omega
  simp [gasketChildPoint, hpx, hpy]

theorem gasketChildPoint_one_two_intersection
    (n : Nat) (p q : GasketLatticePoint)
    (hp : gasketLatticeTriangle n p) (hq : gasketLatticeTriangle n q)
    (h : gasketChildPoint n .corner1 p =
      gasketChildPoint n .corner2 q) :
    gasketChildPoint n .corner1 p =
      (gasketScale n, gasketScale n) := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [gasketLatticeTriangle, gasketChildPoint] at hp hq h
  rcases h with ⟨hx, hy⟩
  have hpx : px = 0 := by omega
  have hpy : py = gasketScale n := by omega
  simp [gasketChildPoint, hpx, hpy]

theorem gasketChildPoint_shared_midpoints (n : Nat) :
    gasketChildPoint n .corner0 (gasketOuterCorner n .corner1) =
        gasketChildPoint n .corner1 (gasketOuterCorner n .corner0) ∧
    gasketChildPoint n .corner0 (gasketOuterCorner n .corner2) =
        gasketChildPoint n .corner2 (gasketOuterCorner n .corner0) ∧
    gasketChildPoint n .corner1 (gasketOuterCorner n .corner2) =
        gasketChildPoint n .corner2 (gasketOuterCorner n .corner1) := by
  simp [gasketChildPoint, gasketOuterCorner]

end PhiGenesis.H10
