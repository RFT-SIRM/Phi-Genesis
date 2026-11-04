module
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

/-!
A minimal smoke test for the pinned Lean/Mathlib toolchain.
This is deliberately separate from the graph-theoretic development.
-/

namespace PhiGenesis.H10

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  norm_num

theorem zmod_two_has_exactly_two_values (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> norm_num

example : Matrix (Fin 2) (Fin 2) (ZMod 2) := 0

end PhiGenesis.H10
