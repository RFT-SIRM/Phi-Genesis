import Mathlib.Tactic
import PhiGenesis.H10.IncidenceForest

/-!
# Injectivity of the triangular hole-row transform

The transformed rows are
  C_u = B_u + B_{u0} + B_{u1} + B_{u2}
at internal addresses and C_u = B_u at terminal addresses.
Summing all transformed rows in a complete descendant subtree telescopes
to the original row at its root.  This gives a constructive left inverse
and proves that the row operation is injective at every finite level.
-/

namespace PhiGenesis.H10

/-- Sum the original row family over a complete ternary address subtree. -/
def gasketAddressRawSubtreeRowSum {E : Type*}
    (C : List (Fin 3) → E → ZMod 2) :
    Nat → List (Fin 3) → E → ZMod 2
  | 0, w, e => C w e
  | k + 1, w, e =>
      C w e
        + gasketAddressRawSubtreeRowSum C k (w ++ [0]) e
        + gasketAddressRawSubtreeRowSum C k (w ++ [1]) e
        + gasketAddressRawSubtreeRowSum C k (w ++ [2]) e

/-- The sum of transformed rows is the raw subtree sum of the family
obtained by applying the triangular row transform to the original rows. -/
theorem gasketAddressSubtreeRowSum_eq_raw {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m k : Nat) (w : List (Fin 3)) :
    gasketAddressSubtreeRowSum B m k w =
      gasketAddressRawSubtreeRowSum
        (fun z => gasketBoundaryRowTransform B m z) k w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
      simp [gasketAddressSubtreeRowSum, gasketAddressRawSubtreeRowSum, ih]

/-- Equal transformed rows give equal sums over every complete descendant
subtree whose leaves lie at address depth m-1. -/
private theorem gasketAddressSubtreeRowSum_congr {E : Type*}
    (B₁ B₂ : List (Fin 3) → E → ZMod 2) (m k : Nat)
    (w : List (Fin 3))
    (hrows : ∀ z, z.length < m →
      gasketBoundaryRowTransform B₁ m z =
        gasketBoundaryRowTransform B₂ m z)
    (hdepth : w.length + k + 1 = m) :
    gasketAddressSubtreeRowSum B₁ m k w =
      gasketAddressSubtreeRowSum B₂ m k w := by
  induction k generalizing w with
  | zero =>
      have hw : w.length < m := by omega
      simpa [gasketAddressSubtreeRowSum] using hrows w hw
  | succ k ih =>
      have h0 : (w ++ [0]).length + k + 1 = m := by
        simp
        omega
      have h1 : (w ++ [1]).length + k + 1 = m := by
        simp
        omega
      have h2 : (w ++ [2]).length + k + 1 = m := by
        simp
        omega
      change
        gasketBoundaryRowTransform B₁ m w
          + gasketAddressSubtreeRowSum B₁ m k (w ++ [0])
          + gasketAddressSubtreeRowSum B₁ m k (w ++ [1])
          + gasketAddressSubtreeRowSum B₁ m k (w ++ [2]) =
        gasketBoundaryRowTransform B₂ m w
          + gasketAddressSubtreeRowSum B₂ m k (w ++ [0])
          + gasketAddressSubtreeRowSum B₂ m k (w ++ [1])
          + gasketAddressSubtreeRowSum B₂ m k (w ++ [2])
      rw [hrows w (by omega),
        ih (w ++ [0]) h0, ih (w ++ [1]) h1, ih (w ++ [2]) h2]

/-- The triangular boundary-row transform is injective on all addresses
of a fixed finite level.  The inverse is obtained by summing transformed
rows over the complete descendant subtree rooted at the address. -/
theorem gasketBoundaryRowTransform_injective_on_addresses {E : Type*}
    (B₁ B₂ : List (Fin 3) → E → ZMod 2) (m : Nat)
    (hrows : ∀ w, w.length < m →
      gasketBoundaryRowTransform B₁ m w =
        gasketBoundaryRowTransform B₂ m w) :
    ∀ w, w.length < m → B₁ w = B₂ w := by
  intro w hw
  have hdepth : w.length + (m - w.length - 1) + 1 = m := by omega
  have hsum :=
    gasketAddressSubtreeRowSum_congr B₁ B₂ m
      (m - w.length - 1) w hrows hdepth
  rw [gasketAddressSubtreeRowSum_eq B₁ m (m - w.length - 1) w hdepth,
    gasketAddressSubtreeRowSum_eq B₂ m (m - w.length - 1) w hdepth] at hsum
  exact hsum

end PhiGenesis.H10
