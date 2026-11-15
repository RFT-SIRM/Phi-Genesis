# Finite-level bottom eigenvalues of the local-face Schur model (theta = 2 pi interpretation conditional)

**Date:** 6 November 2026  
**Status of this note:** finite-level numerical computation from the exact Schur recursion in 260-digit arithmetic. The 145-digit figure below is the numerical value of the level-9 eigenvalue \(\lambda_9\), not a 145-digit evaluation of the infinite-level limit.

**Subsequent Lean result (reviewed 15 November 2026):** the least-eigenvalue sequence of the level-\(N\) Sierpiński signless Laplacian and its gauge-conjugate signed matrix is now proved to converge for \(N\geq6\). Its limit \(\lambda_\infty\) is enclosed in the exact rational interval \([L,U]\) of width \(2\cdot10^{-36}\). See [the proof map](PROOF_MAP.md) and [SchurEigenvalue.lean](../../PhiGenesis/SpectralGap/SchurEigenvalue.lean). This later theorem proves convergence but does not identify the limit with the level-9 decimal expansion or give a closed form.

This note **replaces** the version merged in PR #12, whose conclusions were wrong (see "Correction" below).

Script: [`schur_bottom_eigenvalue.py`](schur_bottom_eigenvalue.py).

## Method

All triangle sign products equal +1, so H = D + A_s is gauge-equivalent to the signless Laplacian
Q = D + A of the Sierpinski graph. Let T_m(lambda) be the boundary Schur matrix obtained by eliminating all
non-corner vertices from Q_m − lambda I while leaving the −lambda shift off
the three retained outer corners. Equivalently, T_m(lambda) = S_m(lambda) +
lambda I_3, where S_m is the ordinary Schur complement of Q_m − lambda I.
Thus the retained corner diagonal starts at the degree inside the piece. It is S3-symmetric, with diagonal
alpha_m and off-diagonal beta_m. Gluing three copies at three midpoints and eliminating the
midpoints gives T_(m+1). The corner modes split into the channels A1: alpha + 2 beta − lambda = 0
and E: alpha − beta − lambda = 0; the bottom eigenvalue is the lowest A1 root. The one-step formulas
are those of `schurNextDiagonal` and `schurNextOffDiagonal` in
`PhiGenesis/SpectralGap/SchurBoundary.lean`, where the recursion is formalized.

Validation: the recursion reproduces the directly diagonalized bottom eigenvalues at levels 1 to 4
to 40 digits (levels 3 and 4 against 40-digit inverse iteration). At level 5, direct diagonalization
returns a vector inside the nearly degenerate A1 + E cluster; its Rayleigh quotient
1.30912892028081342121312… equals A1 + (E − A1)/3 from the recursion to 25 digits.

## Bottom eigenvalue (A1 root)

| level m | dim | lambda_m (40 decimals) |
| ---: | ---: | --- |
| 3 | 42 | 1.3090710652556068404036933845248248253260 |
| 4 | 123 | 1.3091289186270032373372269265507617266049 |
| 5 | 366 | 1.3091289202808134205376249464114593830015 |
| 6 | 1,095 | 1.3091289202808134218886230881708101876508 |
| 7 | 3,282 | 1.3091289202808134218886230881708101885523 |
| 8 | 9,843 | 1.3091289202808134218886230881708101885523 |
| 9 | 29,526 | 1.3091289202808134218886230881708101885523 |

|lambda_9 − lambda_8| = 8·10⁻¹⁴⁶, so lambda_9 = 1.30912892028081342188862308817081018855232425111732634343…
is the bottom eigenvalue of the level-9 graph to about 145 digits.

## Quadratic increment law (observed)

With Delta_m = lambda_m − lambda_(m−1):

| m | Delta_m | Delta_m / Delta_(m−1)² |
| ---: | ---: | ---: |
| 4 | 5.7853371·10⁻⁵ | — |
| 5 | 1.6538102·10⁻⁹ | 0.4941153171 |
| 6 | 1.3509981·10⁻¹⁸ | 0.4939504987 |
| 7 | 9.0155645·10⁻³⁷ | 0.4939504899 |
| 8 | 4.0148495·10⁻⁷³ | 0.4939504899 |
| 9 | 7.961996·10⁻¹⁴⁶ | 0.4939504899 |

The ratio is constant to 10 digits from level 7 on: Delta_(m+1) ≈ c·Delta_m² with c = 0.4939504899
(numerically).

## Splitting of the corner modes

The three corner modes split into one A1 and two E states. With s_m = (E root) − (A1 root):

| m | s_m | s_m / s_(m−1)² |
| ---: | ---: | ---: |
| 4 | 2.4807153·10⁻⁹ | — |
| 5 | 2.0264972·10⁻¹⁸ | 0.32930033 |
| 6 | 1.3523347·10⁻³⁶ | 0.32930033 |
| 7 | 6.0222742·10⁻⁷³ | 0.32930033 |

The splitting obeys the same kind of law, s_(m+1) = c'·s_m² with c' = 0.32930033, and
c / c' = 1.5 to the printed digits. The "three-fold degenerate" cluster at levels 5 to 7 is therefore
only degenerate up to the splitting above.

## Correction

The version of this note merged in PR #12 reported that the increments were not a constant multiple
of the squared previous increment, that levels 5 and 6 differ by 6.8·10⁻¹⁹, and that the ratio fell
from 0.49 to 0.25. These statements came from Rayleigh quotients of double-precision eigenvectors of
the nearly degenerate A1 + E cluster, which mix the two channels at level 5. The true A1 values give
Delta_6 = 1.35·10⁻¹⁸ and a constant ratio 0.494. The retraction of the constant-ratio law was itself
an error and is withdrawn.

## What is and is not established

- **Computed numerically:** finite-level bottom eigenvalues and the \(A_1/E\) splitting from the exact Schur recursion. The level-9 \(A_1\) value is numerically stable to about 145 displayed decimal places. The calculation was validated against direct diagonalization at levels 1–5; its residual diagnostics are numerical, not an outward-rounded interval certificate.
- **Proved in Lean 4:** every real eigenvalue of the signed graph Laplacian is at least \(1\) at every level, and the signed Laplacian is the Gram matrix of a signed incidence matrix.
- **Proved in Lean 4 since this note was written:** for \(N\geq6\), the least eigenvalues of the signless graph Laplacians \(Q_N\), and therefore of their gauge-conjugate signed matrices, converge to \(\lambda_\infty\in[L,U]\). The limit is defined as schurBootstrapA1AtLevel_rootLimit and is a zero of the limiting \(A_1\) characteristic.
- **Not established:** a closed form for \(\lambda_\infty\), a 145-digit certified decimal expansion of \(\lambda_\infty\), the all-level quadratic increment law, or an exact value/interpretation for its coefficient(s) \(c,c'\).
- **Model-identification limitation:** the correspondence between this local-face matrix and the external \(\theta=2\pi\) operator remains conditional; the external sg.py/gap.py sources were not available for direct source-to-source verification.
- A search for an integer polynomial of degree at most 8 with coefficients below \(10^6\) vanishing at \(\lambda_9\) found none. This finite search is not a proof that \(\lambda_9\) or \(\lambda_\infty\) is transcendental or non-algebraic.
