# Precision record of the finite-level Schur calculations

**Status:** finite-level computations and computer-assisted interval certificates for the local-face model $H=D+A_s$ (gauge-equivalent to the signless Sierpiński Laplacian $Q=D+A$). Nothing on this page is a Lean theorem about all levels. The theorem about the limit $\lambda_\infty$ is the Lean enclosure $[L,U]$ of width $2\cdot10^{-36}$ (see [the proof map](PROOF_MAP.md)).

The repository contains calculations at four precision tiers. They answer different questions, and the number of digits used by a method is not the number of digits proved for $\lambda_\infty$.

| Tier | Method | Digits used | Range | What it gives | Status |
|---|---|---:|---|---|---|
| 1 | Exact Schur recursion, standalone script | 260 | $A_1$ to level 9; $E$ to level 7 | Bottom eigenvalue $\lambda_9=1.30912892028081342188862308817081018855232425\ldots$, stable to about 145 digits | Numerical |
| 2 | Exact Schur recursion, `schur_decimation.py` | 1,250 | $A_1$ and $E$ to level 12 | Level increments down to $10^{-1163}$ (table below) | Numerical |
| 3 | Outward-rounded interval arithmetic and Sylvester inertia, `schur_inertia_certificate.py` | 2,450, bracket radius $10^{-2390}$ | $A_1$ and $E$, levels 1–12 (24 brackets) | $A_1$ is the simple lowest eigenvalue and $E$ the doublet next above it, at every level 1–12. Level-12 $E$–$A_1$ separation greater than $9.9\times10^{-2327}$ | Computer-assisted finite-level certificate |
| 4 | Outward-rounded derivative certificate, `schur_derivative_certificate.py` | 10,000, radius $10^{-9400}$ | $A_1$ transitions 5→13 (levels up to 14) | Certified root order, positive pivots, curvature and derivative bounds; the sampled derivative tends to $-1.29328974303045258005\ldots$ | Computer-assisted finite-level certificate |

Independent of the four tiers, a daily workflow solves the full sparse sector matrices directly at 360 digits (see the section on the daily campaign in the [README](../../README.md)). Its recorded runs end with an outer residual of about $10^{-143}$, so it checks the recursion against a direct solve to about 143 digits and does not reach the scales above.

## Level increments of the $A_1$ root (tier 2, 1,250 digits)

$\delta_m=\lambda_m-\lambda_{m-1}$, recomputed with `python computational/spectral_gap_theta_2pi/schur_decimation.py --sector A1 --max-level 12 --dps 1250`:

| $m$ | $\delta_m$ |
|---:|---|
| 9 | $7.9620\times10^{-146}$ |
| 10 | $3.1313\times10^{-291}$ |
| 11 | $4.8433\times10^{-582}$ |
| 12 | $1.1587\times10^{-1163}$ |

The increments obey $\delta_{m+1}\approx c\,\delta_m^2$ with $c=0.4939504899\ldots$ (observed; not proved for all levels). The level-10 increment, about $3.1\times10^{-291}$, is therefore already resolved by the exact recursion. The same recursion gives the $E_9-A_{1,9}$ splitting at about $4.7\times10^{-291}$ (see the [research log](RESEARCH_LOG_2026-11-05.md), section 39).

## What the 2,450-digit certificate proves, and what it does not

**Proves (finite-level, computer-assisted):** for each level $m=1,\dots,12$ the $A_1$ boundary root and the $E$ boundary root are each enclosed in a bracket of radius $10^{-2390}$ with a sign change at the exact decimal endpoints and a strictly negative characteristic derivative throughout; every midpoint-pivot eigenvalue has a lower bound above $1.1516$; by Sylvester inertia the $A_1$ root is the simple global smallest eigenvalue of $Q_m$ and the $E$ root is the second eigenvalue with multiplicity two. All endpoint operations use explicit floor and ceiling rounding.

**Does not prove:** convergence as the level tends to infinity, the quadratic increment law for all levels, a closed form for $\lambda_\infty$, or identification of the local-face matrix with the external $\theta=2\pi$ operator. $\lambda_\infty$ is proved only to the 36 digits of the Lean enclosure $[L,U]$. If the observed quadratic law persisted, $\lambda_{12}$ would approximate $\lambda_\infty$ to about 2,300 digits; that is a consequence of an unproved law, not a result.

## Reproduction (recorded 18 November 2026)

| Command | Result in a local run |
|---|---|
| `python computational/spectral_gap_theta_2pi/schur_inertia_certificate.py --max-level 12 --dps 2450 --radius-digits 2390` | Levels 1–12 certified, about 11 seconds |
| `python computational/spectral_gap_theta_2pi/schur_decimation.py --sector A1 --max-level 12 --dps 1250` | Increments as in the table above, under 1 second |
| `python computational/spectral_gap_theta_2pi/schur_derivative_certificate.py --max-level 14 --start-level 5 --dps 10000 --radius-digits 9400` | `SUCCESS: transitions 5..13 have certified root order, positive pivots, curvature, and derivative bounds`, a few minutes |
| `pytest -q test_spectral_schur_inertia.py test_schur_bottom_eigenvalue.py test_spectral_schur_derivative_certificate.py` | 27 passed |

The interval/inertia certificate is also part of the ordinary test suite (`test_spectral_schur_inertia.py` runs the full 12-level certificate from scratch). The derivative certificate has its own workflow, which is started manually; it is not part of the daily schedule.
