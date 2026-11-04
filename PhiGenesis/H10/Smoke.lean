module
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
A small build smoke test for the pinned Lean/Mathlib environment.
The mathematical development starts in separate modules after this target builds.
-/

namespace PhiGenesis.H10

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  calc
    (1 : ZMod 2) + 1 = 2 := by ring
    _ = 0 := ZMod.natCast_self 2

theorem zmod_two_has_exactly_two_values (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

example : Matrix (Fin 2) (Fin 2) (ZMod 2) := 0

end PhiGenesis.H10
