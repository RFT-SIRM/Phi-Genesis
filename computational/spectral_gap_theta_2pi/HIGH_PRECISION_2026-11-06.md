# High-precision bottom eigenvalue, theta = 2 pi local-face model

**Date:** 6 November 2026
**Status:** numerical observation. Nothing here is a proof.

Script: [`bottom_eigenvalue_hp.py`](bottom_eigenvalue_hp.py). For each level it takes the three lowest
eigenvectors in double precision and evaluates the Rayleigh quotient in 40-digit arithmetic. By the
variational principle every value is an upper bound for the bottom eigenvalue of H at that level.

| level m | dim | bottom eigenvalue (20 decimals) | Δ_m = λ_m − λ_(m−1) |
| ---: | ---: | --- | ---: |
| 3 | 42 | 1.30907106525560684040 | — |
| 4 | 123 | 1.30912891862700323733 | 5.785337·10⁻⁵ |
| 5 | 366 | 1.30912892028081342121 | 1.653810·10⁻⁹ |
| 6 | 1,095 | 1.30912892028081342188 | 6.7794·10⁻¹⁹ |
| 7 | 3,282 | 1.30912892028081342188 | below 10⁻³⁰ |
| 8 | 9,843 | 1.30912892028081342188 | below 10⁻³⁰ |

Levels 6, 7 and 8 agree to 30 digits: 1.30912892028081342188862308817. This is the value of the
bottom eigenvalue at these levels, an upper bound on the true limit.

## What this shows and what it does not

- The bottom eigenvalue keeps increasing after level 5. It is **not** exactly constant from level 5:
  levels 5 and 6 differ by 6.8·10⁻¹⁹. Earlier double-precision runs showed no change because that
  difference is below machine precision.
- The increments shrink faster than geometrically: log₁₀ Δ_m is −4.24, −8.78, −18.17, so the exponent
  grows by a factor of about 2.07 per level.
- The ratio Δ_m / Δ_(m−1)² is 0.512 at m = 4 (from the earlier table), 0.494 at m = 5 and 0.248 at m = 6.
  It is **not constant**, so no law of the form Δ_(m+1) = c·Δ_m² is supported. This note retracts the
  informal estimate c ≈ 0.5.
- The bottom eigenspace at levels 5 and 6 is carried by three modes, one per corner, whose weight
  decays away from the corner but is not compactly supported. A 52-vertex block cut around one corner
  gives a characteristic polynomial whose relevant root, 1.3091289202864…, differs from the
  eigenvalue in the 11th digit. The block is therefore not an exact invariant subspace.
- Not established: convergence of λ_m, the value of the limit beyond the digits above, and any closed
  form for it. The Lean result (every real eigenvalue is at least 1) is unaffected.

## Precision note

At level 5 the script's Rayleigh quotient is about 2.4·10⁻²¹ above the value from three steps of
inverse iteration in 50-digit arithmetic (1.309128920280813421210682…), because the double-precision
eigenvector of the three-fold cluster is less accurate there. The table uses the inverse-iteration
value at level 5, so Δ_6 = 6.7794·10⁻¹⁹; the script prints 6.7550·10⁻¹⁹. The conclusions above do not
depend on this difference.
