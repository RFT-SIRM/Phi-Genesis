import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurCornerResponse

namespace PhiGenesis.SpectralGap

/-- The scalar Schur trajectory is the corner response of the graph matrix,
as long as both pivots are nonzero at every level used. -/
theorem sgCornerResponse_trajectory (lam : ℝ) :
    ∀ N : ℕ,
      (∀ n < N,
        schurMidpointPivot (schurBoundaryTrajectory lam (2 - lam, 1) n).1
          (schurBoundaryTrajectory lam (2 - lam, 1) n).2 lam ≠ 0 ∧
        schurMidpointPivot (schurBoundaryTrajectory lam (2 - lam, 1) n).1
          (schurBoundaryTrajectory lam (2 - lam, 1) n).2 lam +
          3 * (schurBoundaryTrajectory lam (2 - lam, 1) n).2 ≠ 0) →
      SgCornerResponse N lam (schurBoundaryTrajectory lam (2 - lam, 1) N).1
        (schurBoundaryTrajectory lam (2 - lam, 1) N).2 := by
  intro N
  induction N with
  | zero =>
      intro _
      simpa [schurBoundaryTrajectory] using sgCornerResponse_zero lam
  | succ N ih =>
      intro hpiv
      have h := ih (fun n hn => hpiv n (Nat.lt_succ_of_lt hn))
      obtain ⟨hc, hc3⟩ := hpiv N (Nat.lt_succ_self N)
      set a := (schurBoundaryTrajectory lam (2 - lam, 1) N).1 with ha
      set b := (schurBoundaryTrajectory lam (2 - lam, 1) N).2 with hb
      have e : schurMidpointPivot a b lam = 2 * a + lam - b := rfl
      rw [e] at hc hc3
      have key := sgCornerResponse_succ N lam a b h hc hc3
      have hstep : schurBoundaryTrajectory lam (2 - lam, 1) (N + 1) =
          (schurNextDiagonal a b (2 * a + lam - b),
           schurNextOffDiagonal b (2 * a + lam - b)) := rfl
      rw [hstep]
      exact key

/-- In the bootstrap window the scalar Schur trajectory is the corner response of the
graph matrix at every level; the pivot nonvanishing is already proved. -/
theorem sgCornerResponse_trajectory_bootstrap (lam : ℝ)
    (hlam : lam ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) (N : ℕ) :
    SgCornerResponse N lam (schurBoundaryTrajectory lam (2 - lam, 1) N).1
      (schurBoundaryTrajectory lam (2 - lam, 1) N).2 :=
  sgCornerResponse_trajectory lam N (fun n _ => schurBootstrap_all_pivots_nonzero lam hlam n)

end PhiGenesis.SpectralGap
