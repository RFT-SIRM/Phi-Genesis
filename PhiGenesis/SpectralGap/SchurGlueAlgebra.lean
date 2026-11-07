import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurBoundary

/-!
# Bridge, step B2b (algebraic half): one gluing step on three midpoints

Three copies of a level-`m` cell are glued at three midpoints.  Each copy has corner
Schur matrix with diagonal `a` and off-diagonal `b` (the spectral shift included in `a`).
With `c = 2a + lam - b` the midpoint block is `c I + b J`.  For prescribed values `z1 z2 z3`
at the outer corners, the midpoint values below solve the three interior equations, and the
resulting corner response is the matrix `(schurNextDiagonal, schurNextOffDiagonal)`.
-/

namespace PhiGenesis.SpectralGap

/-- Value at the midpoint opposite to the corner with value `z`, for corner total `s`. -/
noncomputable def schurGlueMid (b c s z : ℝ) : ℝ :=
  -(b / c) * ((c + b) / (c + 3 * b) * s - z)

/-- The interior equation at one midpoint: diagonal `c + b`, coupling `b` to the other two
midpoints and to its two adjacent outer corners `z1`, `z2`. -/
theorem schurGlue_midpoint_row (b c z1 z2 z3 s : ℝ)
    (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) (hs : s = z1 + z2 + z3) :
    (c + b) * schurGlueMid b c s z3 + b * schurGlueMid b c s z2 +
      b * schurGlueMid b c s z1 + b * (z1 + z2) = 0 := by
  have h3a : c + b * 3 ≠ 0 := by intro h; apply hc3; linarith
  have h3b : b * 3 + c ≠ 0 := by intro h; apply hc3; linarith
  have h3c : 3 * b + c ≠ 0 := by intro h; apply hc3; linarith
  subst hs
  unfold schurGlueMid
  field_simp
  ring

/-- Response at an outer corner: its own diagonal `a` plus coupling `b` to its two midpoints
equals the next Schur matrix applied to the corner values. -/
theorem schurGlue_corner_response (a b c z1 z2 z3 s : ℝ)
    (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) (hs : s = z1 + z2 + z3) :
    a * z1 + b * (schurGlueMid b c s z3 + schurGlueMid b c s z2) =
      schurNextDiagonal a b c * z1 + schurNextOffDiagonal b c * z2 +
        schurNextOffDiagonal b c * z3 := by
  have h3a : c + b * 3 ≠ 0 := by intro h; apply hc3; linarith
  have h3b : b * 3 + c ≠ 0 := by intro h; apply hc3; linarith
  have h3c : 3 * b + c ≠ 0 := by intro h; apply hc3; linarith
  subst hs
  unfold schurGlueMid schurNextDiagonal schurNextOffDiagonal
  field_simp
  ring

end PhiGenesis.SpectralGap
