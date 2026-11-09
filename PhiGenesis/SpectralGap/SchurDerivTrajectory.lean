import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSignedTransfer

namespace PhiGenesis.SpectralGap

/-- The parameter derivatives `(a_k', b_k')` of the Schur trajectory, by the exact
derivative recursion. -/
noncomputable def schurDerivTrajectory (lam : ℝ) : ℕ → ℝ × ℝ
  | 0 => (-1, 0)
  | n + 1 =>
      (schurNextDiagonalParameterDerivative
          (schurBoundaryTrajectory lam (2 - lam, 1) n).2
          (schurMidpointPivot (schurBoundaryTrajectory lam (2 - lam, 1) n).1
            (schurBoundaryTrajectory lam (2 - lam, 1) n).2 lam)
          (schurDerivTrajectory lam n).1 (schurDerivTrajectory lam n).2
          (2 * (schurDerivTrajectory lam n).1 + 1 - (schurDerivTrajectory lam n).2),
       schurNextOffDiagonalParameterDerivative
          (schurBoundaryTrajectory lam (2 - lam, 1) n).2
          (schurMidpointPivot (schurBoundaryTrajectory lam (2 - lam, 1) n).1
            (schurBoundaryTrajectory lam (2 - lam, 1) n).2 lam)
          (schurDerivTrajectory lam n).2
          (2 * (schurDerivTrajectory lam n).1 + 1 - (schurDerivTrajectory lam n).2))

/-- The trajectory is differentiable in the parameter with derivative `schurDerivTrajectory`,
as long as all preceding pivot pairs are nonzero. -/
theorem schurBoundaryTrajectory_hasDerivAt (lam0 : ℝ) :
    ∀ n : ℕ,
      (∀ k, k < n →
        schurMidpointPivot (schurBoundaryTrajectory lam0 (2 - lam0, 1) k).1
          (schurBoundaryTrajectory lam0 (2 - lam0, 1) k).2 lam0 ≠ 0 ∧
        schurMidpointPivot (schurBoundaryTrajectory lam0 (2 - lam0, 1) k).1
          (schurBoundaryTrajectory lam0 (2 - lam0, 1) k).2 lam0 +
          3 * (schurBoundaryTrajectory lam0 (2 - lam0, 1) k).2 ≠ 0) →
      HasDerivAt (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).1)
        (schurDerivTrajectory lam0 n).1 lam0 ∧
      HasDerivAt (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).2)
        (schurDerivTrajectory lam0 n).2 lam0 := by
  intro n
  induction n with
  | zero =>
      intro _
      constructor
      · exact ((hasDerivAt_const lam0 (2 : ℝ)).sub (hasDerivAt_id' lam0)).congr_deriv
          (by norm_num [schurDerivTrajectory])
      · exact hasDerivAt_const lam0 (1 : ℝ)
  | succ n ih =>
      intro hden
      obtain ⟨ha, hb⟩ := ih (fun k hk => hden k (Nat.lt_succ_of_lt hk))
      obtain ⟨hc0, hc3⟩ := hden n (Nat.lt_succ_self n)
      have hc : HasDerivAt
          (fun y => schurMidpointPivot (schurBoundaryTrajectory y (2 - y, 1) n).1
            (schurBoundaryTrajectory y (2 - y, 1) n).2 y)
          (2 * (schurDerivTrajectory lam0 n).1 + 1 - (schurDerivTrajectory lam0 n).2) lam0 :=
        ((ha.const_mul 2).add (hasDerivAt_id' lam0)).sub hb
      have key := schurNextPair_deriv_formula
        (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).1)
        (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).2)
        (fun y => schurMidpointPivot (schurBoundaryTrajectory y (2 - y, 1) n).1
          (schurBoundaryTrajectory y (2 - y, 1) n).2 y)
        lam0 _ _ _ ha hb hc hc0 hc3
      have diff := schurNextPair_differentiableAt_of_hasDerivAt
        (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).1)
        (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).2)
        (fun y => schurMidpointPivot (schurBoundaryTrajectory y (2 - y, 1) n).1
          (schurBoundaryTrajectory y (2 - y, 1) n).2 y)
        lam0 _ _ _ ha hb hc hc0 hc3
      exact ⟨diff.1.hasDerivAt.congr_deriv key.1, diff.2.hasDerivAt.congr_deriv key.2⟩

/-- In the bootstrap window the trajectory is differentiable at every level. -/
theorem schurBoundaryTrajectory_hasDerivAt_bootstrap (lam : ℝ)
    (hlam : lam ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper) (n : ℕ) :
    HasDerivAt (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).1)
        (schurDerivTrajectory lam n).1 lam ∧
      HasDerivAt (fun y => (schurBoundaryTrajectory y (2 - y, 1) n).2)
        (schurDerivTrajectory lam n).2 lam :=
  schurBoundaryTrajectory_hasDerivAt lam n
    (fun k _ => ⟨(schurBootstrap_all_pivots_pos lam hlam k).1.ne',
      (schurBootstrap_all_pivots_pos lam hlam k).2.ne'⟩)

end PhiGenesis.SpectralGap
