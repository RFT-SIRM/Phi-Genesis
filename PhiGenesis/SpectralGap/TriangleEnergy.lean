import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Local triangle energy for the signed-face model

For one upward triangle, the three signed-edge contributions reduce after
vertex gauge to the three pair sums. This file records the exact scalar
identity and its finite-coordinate extension. The next module will sum this
local identity over an edge-disjoint face partition of the Sierpinski graph.
-/

namespace PhiGenesis.SpectralGap

/-- Exact energy identity on one triangle. -/
theorem trianglePairEnergy_identity (x y z : ℝ) :
    (x + y) ^ 2 + (x + z) ^ 2 + (y + z) ^ 2 =
      x ^ 2 + y ^ 2 + z ^ 2 + (x + y + z) ^ 2 := by
  ring

/-- The pair energy on one triangle dominates the sum of the three vertex energies. -/
theorem trianglePairEnergy_lower_bound (x y z : ℝ) :
    x ^ 2 + y ^ 2 + z ^ 2 ≤
      (x + y) ^ 2 + (x + z) ^ 2 + (y + z) ^ 2 := by
  rw [trianglePairEnergy_identity]
  nlinarith [sq_nonneg (x + y + z)]

/-- The exact triangle identity, summed over finitely many real coordinates. -/
theorem trianglePairEnergy_identity_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y z : ι → ℝ) :
    (∑ i, ((x i + y i) ^ 2 + (x i + z i) ^ 2 + (y i + z i) ^ 2)) =
      (∑ i, (x i) ^ 2) + (∑ i, (y i) ^ 2) + (∑ i, (z i) ^ 2) +
        (∑ i, (x i + y i + z i) ^ 2) := by
  classical
  calc
    (∑ i, ((x i + y i) ^ 2 + (x i + z i) ^ 2 + (y i + z i) ^ 2)) =
        ∑ i, ((x i) ^ 2 + (y i) ^ 2 + (z i) ^ 2 +
          (x i + y i + z i) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact trianglePairEnergy_identity (x i) (y i) (z i)
    _ = (∑ i, (x i) ^ 2) + (∑ i, (y i) ^ 2) +
          (∑ i, (z i) ^ 2) + (∑ i, (x i + y i + z i) ^ 2) := by
            simp only [Finset.sum_add_distrib]

/-- Finite-coordinate triangle energy dominates the total vertex energy. -/
theorem trianglePairEnergy_lower_bound_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y z : ι → ℝ) :
    (∑ i, (x i) ^ 2) + (∑ i, (y i) ^ 2) + (∑ i, (z i) ^ 2) ≤
      ∑ i, ((x i + y i) ^ 2 + (x i + z i) ^ 2 + (y i + z i) ^ 2) := by
  rw [trianglePairEnergy_identity_pi]
  have hnonneg : 0 ≤ ∑ i, (x i + y i + z i) ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg (x i + y i + z i)
  linarith

end PhiGenesis.SpectralGap
