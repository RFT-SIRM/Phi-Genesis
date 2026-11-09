import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurEigenvalue

namespace PhiGenesis.SpectralGap

/-- Exact value of the next-level A1 characteristic at a root of the current level. -/
theorem sgA1_next_at_root (n : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel r n = 0) :
    schurBootstrapA1AtLevel r (n + 1) =
      -2 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 * r /
        (r - 2 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2) := by
  have hpiv := schurBootstrap_all_pivots_pos r hr (6 + n)
  have hstep : schurBoundaryTrajectory r (2 - r, 1) (6 + (n + 1)) =
      schurBoundaryStateStep r (schurBoundaryTrajectory r (2 - r, 1) (6 + n)) := rfl
  unfold schurBootstrapA1AtLevel at hroot ⊢
  rw [hstep]
  generalize schurBoundaryTrajectory r (2 - r, 1) (6 + n) = S at hroot hpiv ⊢
  obtain ⟨a, b⟩ := S
  simp only [schurBoundaryStateStep] at ⊢
  dsimp only at hroot hpiv ⊢
  have hc := schurMidpointPivot_eq_lambda_sub_five_b_at_A1_root a b r hroot
  have key := schurNextA1_at_old_root a b (schurMidpointPivot a b r) hroot
    hpiv.1.ne' hpiv.2.ne'
  rw [key, hc]
  rw [show r - 5 * b + 5 * b = r by ring, show r - 5 * b + 3 * b = r - 2 * b by ring]

/-- Exact value of the off-diagonal state of the next level at a root of the current level. -/
theorem sgB_next_at_root (n : ℕ) (r : ℝ)
    (hroot : schurBootstrapA1AtLevel r n = 0) :
    (schurBoundaryTrajectory r (2 - r, 1) (6 + (n + 1))).2 =
      -(schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 ^ 2 *
        (r - 6 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2) /
        ((r - 5 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2) *
          (r - 2 * (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2)) := by
  have hstep : schurBoundaryTrajectory r (2 - r, 1) (6 + (n + 1)) =
      schurBoundaryStateStep r (schurBoundaryTrajectory r (2 - r, 1) (6 + n)) := rfl
  unfold schurBootstrapA1AtLevel at hroot
  rw [hstep]
  generalize schurBoundaryTrajectory r (2 - r, 1) (6 + n) = S at hroot ⊢
  obtain ⟨a, b⟩ := S
  simp only [schurBoundaryStateStep]
  dsimp only at hroot ⊢
  have hc := schurMidpointPivot_eq_lambda_sub_five_b_at_A1_root a b r hroot
  unfold schurNextOffDiagonal
  rw [hc]
  rw [show r - 5 * b - b = r - 6 * b by ring, show r - 5 * b + 3 * b = r - 2 * b by ring]

/-- At a root of level `6 + n` the next-level A1 characteristic is nonnegative. -/
theorem sgA1_next_at_root_nonneg (n : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel r n = 0) :
    0 ≤ schurBootstrapA1AtLevel r (n + 1) := by
  rw [sgA1_next_at_root n r hr hroot]
  have hwin := schurBootstrapEndpoints_in_parameter_window
  have hl : (1309 / 1000 : ℝ) ≤ r := le_trans hwin.1 hr.1
  have hu : r ≤ (131 / 100 : ℝ) := le_trans hr.2 hwin.2.2.2
  have hstart := schurBootstrap_levelThree_state_box r hr
  have hstate := schurBoundaryTrajectory_coarse_state_box r
    (schurBoundaryTrajectory r (2 - r, 1) 3).1
    (schurBoundaryTrajectory r (2 - r, 1) 3).2
    hstart.1 hstart.2.1 hstart.2.2 hl hu (3 + n)
  have e : 6 + n = 3 + (3 + n) := by omega
  have htraj : schurBoundaryTrajectory r (2 - r, 1) (6 + n) =
      schurBoundaryTrajectory r (schurBoundaryTrajectory r (2 - r, 1) 3) (3 + n) := by
    rw [e, schurBoundaryTrajectory_add]
  have hb : (schurBoundaryTrajectory r (2 - r, 1) (6 + n)).2 ≤ 0 := by
    rw [htraj]; exact hstate.2.2
  apply div_nonneg
  · nlinarith [mul_nonneg (neg_nonneg.2 hb) (show (0 : ℝ) ≤ r by linarith)]
  · linarith

end PhiGenesis.SpectralGap
