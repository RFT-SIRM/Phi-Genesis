# Proof map: limiting least eigenvalue of the Sierpiński signless Laplacian (Lean)

**Status reviewed: 15 November 2026.** The Lean development proves that the least eigenvalue of the level-$N$ signless Laplacian $Q_N$, and of its gauge-conjugate signed matrix, converges for every sequence of levels $N=6+n$. The limit is the Lean-defined real number schurBootstrapA1AtLevel_rootLimit and satisfies the exact rational enclosure below.

$$
L=\frac{1309128920280813421888623088170810187}{10^{36}},
\qquad
U=\frac{1309128920280813421888623088170810189}{10^{36}},
\qquad
U-L=2\cdot10^{-36}.
$$

$$
\lambda_\infty\in[L,U].
$$

This is a formal existence-and-enclosure result. It does **not** provide a closed form or certify 145 decimal places of the limit. The approximately 145-digit number in the high-precision note is the numerical finite-level value $\lambda_9$.

| Step | Statement | Lean theorem(s) | File |
|---|---|---|---|
| gauge | Signed and signless graph Laplacians are conjugate by the diagonal vertex gauge. | sgSignedLaplacianMatrix_eq_gauge_conj | SchurBridge.lean |
| level 0 | $Q_0-\lambda I$ has diagonal $2-\lambda$ and off-diagonal $1$, giving the recursion start state. | sgSignlessShifted_zero | SchurBridgeLevelZero.lean |
| gluing algebra | Exact three-midpoint gluing equations give the one-step Schur update. | schurGlue_midpoint_row, schurGlue_corner_response | SchurGlueAlgebra.lean |
| combinatorics | A level-$N+1$ graph is assembled from three level-$N$ child cells; the shifted quadratic form decomposes accordingly. | sgSignlessLaplacianMatrix_eq_childSlotSum, sgSignlessShiftedBilinearForm_childDecomposition | SchurSlots.lean |
| corner response | The Schur boundary response of the graph matrix obeys the exact scalar recursion. | sgCornerResponse_zero, sgCornerResponse_succ | SchurCornerResponse.lean |
| trajectory bridge | In the bootstrap interval, the scalar Schur trajectory is the graph-matrix corner response at every level. | sgCornerResponse_trajectory_bootstrap | SchurCornerTrajectory.lean |
| pivots | Every midpoint pivot is strictly positive throughout the exact bootstrap interval. | schurBootstrap_all_pivots_pos | SchurBoundary.lean |
| Dirichlet form | The shifted form is nonnegative on vectors that vanish at the three outer corners. | sgDirichletNonneg_bootstrap | SchurInertiaStep.lean |
| endpoint interval | At $L$ the shifted form is nonnegative on all vectors; at $U$ there is a negative direction. | sgSpectralBounds_bootstrap | SchurSpectralBounds.lean |
| root uniqueness | The $A_1$ root in $[L,U]$ is unique at every level $6+n$. | schurBootstrapA1Root_unique | SchurLambdaMin.lean |
| least eigenvalue | The selected $A_1$ root is the least eigenvalue of $Q_{6+n}$. | sgBottomEigenvalue_atRoot, sgChosenRoot_isLeast | SchurEigenvalue.lean |
| convergence | The least eigenvalues converge to $\lambda_\infty\in[L,U]$. | sgLeastEigenvalue_converges | SchurEigenvalue.lean |
| limiting characteristic | $\lambda_\infty$ is a zero of the uniformly limiting $A_1$ characteristic. | schurBootstrapA1AtLevel_rootLimit_is_root | SchurBoundary.lean |
| signed matrix | The convergence result transfers to the signed matrix by gauge equivalence. | sgSignedEigenSet_eq, sgSignedLeastEigenvalue_converges | SchurSignedTransfer.lean |
| derivatives | The parameter derivative of the Schur trajectory is formalized. | schurBoundaryTrajectory_hasDerivAt_bootstrap | SchurDerivTrajectory.lean |

## Results that remain open

- **Closed form / exact numerical identification:** no closed-form expression for $\lambda_\infty$ is established. The 36-decimal rational interval is rigorous; the level-9 145-digit decimal is a finite-level numerical result, not a certified expansion of the limit.
- **Quadratic root-shift law:** the relation $\delta_{m+1}\sim c\,\delta_m^2$ and existence/value of $c$ remain supported by high-precision numerical evidence, not an all-level Lean theorem. The derivative recursion is formalized, but the required uniform derivative and asymptotic estimates are not.
- **External operator identification:** the repository proves the results for the specified recursive Sierpiński graph matrices. It does not prove that this construction is source-identical to the external $\theta=2\pi$ operator.
- **Low starting levels:** the Lean convergence theorem is stated for $N\geq6$. The finite-level interval/inertia script separately checks levels 1–12; that finite computer-assisted certificate is not an all-level Lean theorem.

## Finite-level numerical certificate (separate from Lean)

The script computational/spectral_gap_theta_2pi/schur_inertia_certificate.py uses outward-rounded Decimal interval arithmetic to certify the ordering of the $A_1$ ground state and $E$ first-excited doublet at each level 1–12. This is a finite computer-assisted proof and must not be described as a Lean-kernel theorem or an infinite-level proof.

## Scope

All theorems in the table concern sgSignlessLaplacianMatrix N and sgSignedLaplacianMatrix N for the recursively defined level-$N$ Sierpiński graph. The uniform lower bound $\lambda_{\min}(N)\geq1$ is proved separately for every level. The convergence theorem concerns the least-eigenvalue sequence on levels $N=6+n$. No closed form, all-level quadratic correction law, or external-model identification is claimed.