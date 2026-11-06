# Bottom eigenvalue of the theta = 2 pi local-face model by exact Schur recursion

**Date:** 6 November 2026
**Status:** numerical observation from an exact recursion in 260-digit arithmetic. No convergence
proof and no closed form for the limit are claimed. This note **replaces** the version merged in
PR #12, whose conclusions were wrong (see "Correction" below).

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
and E: alpha − beta − lambda = 0; the bottom eigenvalue is the lowest A1 root. This is the structure
formalized in `PhiGenesis/SpectralGap/SchurBoundary.lean`.

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

## Quadratic convergence

With Delta_m = lambda_m − lambda_(m−1):

| m | Delta_m | Delta_m / Delta_(m−1)² |
| ---: | ---: | ---: |
| 4 | 5.7853371·10⁻⁵ | — |
| 5 | 1.6538102·10⁻⁹ | 0.4941153171 |
| 6 | 1.3509981·10⁻¹⁸ | 0.4939504987 |
| 7 | 9.0155645·10⁻³⁷ | 0.4939504899 |
| 8 | 4.0148495·10⁻⁷³ | 0.4939504899 |
| 9 | 7.961996·10⁻¹⁴⁶ | 0.4939504899 |

The ratio is constant to 10 digits from level 7 on: Delta_(m+1) = c·Delta_m² with c = 0.4939504899
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

- Computed: the bottom eigenvalue of the level-m graph to 145 digits for m ≤ 9, the constant
  quadratic ratio, and the splitting law. All from an exact recursion validated against direct
  diagonalization at levels 1 to 5.
- Established in Lean 4: every real eigenvalue of the signed Laplacian is at least 1, for every
  level, and the signed Laplacian is the Gram matrix of a signed incidence matrix.
- Not established: that lambda_m converges (the quadratic law makes it overwhelmingly likely but is
  not a proof), a closed form for the limit, or an interpretation of c and c'. A search for an
  integer polynomial of degree at most 8 with coefficients below 10⁶ vanishing at lambda_9 found none.
