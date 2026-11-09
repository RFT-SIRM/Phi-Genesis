# Proof map: bottom of the spectrum of the Sierpinski signless Laplacian (Lean)

Status as of 2026-11-07. All items below are Lean 4 theorems in `PhiGenesis/SpectralGap/` with only the axioms
`propext`, `Classical.choice`, `Quot.sound` and no `sorry`. Everything concerns the matrices
`sgSignlessLaplacianMatrix N` and `sgSignedLaplacianMatrix N` of the level-N Sierpinski graph.

| Step | Statement | Theorem(s) | File |
|---|---|---|---|
| gauge | signed matrix = diag(g) * signless matrix * diag(g) | `sgSignedLaplacianMatrix_eq_gauge_conj` | SchurBridge |
| level 0 | `Q_0 - lam I` has entries `2 - lam` and `1` | `sgSignlessShifted_zero` | SchurBridgeLevelZero |
| gluing algebra | one three-midpoint gluing step | `schurGlue_midpoint_row`, `schurGlue_corner_response` | SchurGlueAlgebra |
| combinatorics | level N+1 = three level-N children glued at three midpoints | `sgSignlessLaplacianMatrix_eq_childSlotSum`, `sgSignlessShiftedBilinearForm_childDecomposition` | SchurSlots |
| rows | parent rows at midpoints and outer corners from child rows | `sgShiftedRow_two_children`, `sgShiftedRow_midpoint01`, `sgShiftedRow_outerLeft` | SchurGlueRows |
| corner response | Schur step for the graph matrix | `sgCornerResponse_zero`, `sgCornerResponse_succ` | SchurCornerResponse |
| trajectory | scalar recursion = corner response of `Q_N - lam I` | `sgCornerResponse_trajectory_bootstrap` | SchurCornerTrajectory |
| pivots | all pivots positive in the 36-digit window | `schurBootstrap_all_pivots_pos` | SchurBoundary |
| Dirichlet form | form nonnegative on vectors vanishing at the corners | `sgDirichletNonneg_bootstrap` | SchurInertiaStep |
| interval | `L <= bottom <= U` for N >= 6 (quadratic-form statement) | `sgSpectralBounds_bootstrap` | SchurSpectralBounds |
| uniqueness | the A1 root of level 6+n in the window is unique | `schurBootstrapA1Root_unique` | SchurLambdaMin |
| eigenvalue | the root is the least eigenvalue of `Q_{6+n}` | `sgChosenRoot_isLeast` | SchurEigenvalue |
| convergence | least eigenvalues converge into the window | `sgLeastEigenvalue_converges`, `schurBootstrapA1AtLevel_rootLimit_is_root` | SchurEigenvalue, SchurBoundary |
| signed matrix | same eigenvalues for the signed matrix | `sgSignedEigenSet_eq`, `sgSignedLeastEigenvalue_converges` | SchurSignedTransfer |
| root identities | exact next-level formulas at a root | `sgA1_next_at_root`, `sgB_next_at_root` | SchurQuadStage1 |
| derivatives | derivative recursion of the trajectory in the parameter | `schurBoundaryTrajectory_hasDerivAt_bootstrap` | SchurDerivTrajectory |

## Not proved

- The quadratic increment law `delta_{m+1} ~ c delta_m^2` and the existence of `c`: numerical evidence only
  (`quadratic_law_check.py`: ratio 0.4939504899, `f'` = -1.29328974303, `c = |f'| / (2 lambda)`).
  A proof needs two-sided bounds on the parameter derivatives along the trajectory over the window
  (the derivative recursion above is the first ingredient).
- Levels `N < 6`.
- A closed form for the limit.
- That these matrices are the operator of the theta = 2 pi model: nothing in this repository proves it.
