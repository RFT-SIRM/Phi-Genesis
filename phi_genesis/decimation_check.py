"""Gate A: rigorous verification of the spectral decimation theorem
(Fukushima-Shima) for the pre-fractal Sierpinski-gasket graph Laplacian
used throughout this repository.

The theorem: eigenvalues of the level-(m-1) graph Laplacian and level-m
graph Laplacian are related by the decimation polynomial
    phi(x) = x*(5 - x)
Specifically, for a GENERIC (non-exceptional) eigenvalue mu of level
m-1, its two preimages under phi (roots of x^2 - 5x + mu = 0) are both
eigenvalues of level m.

The naive test previously in this repo (`decimation_ratio`, checked by
`test_decimation_factor_5`) only checks that the ratio of same-rank
sorted eigenvalues approaches 5 -- a weak, aggregate sanity check, not
a test of the actual theorem.

THIS MODULE tests the real theorem via proper one-to-one (Hungarian
algorithm) bipartite matching between predicted preimages and actual
level-m eigenvalues -- no eigenvalue is allowed to satisfy two demands
at once, unlike a naive nearest-neighbor check.

HONEST RESULT (see test_decimation_gate_a.py; numbers measured at levels 5-7 with dense
floating-point eigenvalues from numpy.linalg.eigvalsh, not exact arithmetic):
  - Matched residuals fall into two separated populations. One is at machine precision
    (largest residual 1.2e-14 / 2.0e-14 / 5.2e-14 at levels 5 / 6 / 7); every other
    residual is at least 8.1e-5 / 5.4e-6 / 3.6e-7. Where a target is matched at machine
    precision, the polynomial relation holds to that precision. The gap between the two
    populations narrows with level, so tol_machine below is a measured choice for
    levels 5-7, not a guarantee for higher levels.
  - The MACHINE-EXACT RATE is well below 100% at low levels (level 5: 38%, level 6:
    57%, level 7: 71%) even after excluding the three classically known exceptional
    values {2, 5, 6}, and it increases with level. Whether the unmatched remainder is
    the recursively generated exceptional set of the theory (preimages of exceptional
    values are themselves exceptional; its relative share shrinks with level), an effect
    of the corner-degree-2 boundary of this Laplacian (see README, Open Problem #2), or
    both, is NOT decided here. This module implements the simple (non-recursive)
    exclusion only; Gate A is not closed.
  - The broad classification tolerance tol_exact (default 1e-4) also admits "near-miss"
    pairs, residual between tol_machine and tol_exact, that are not machine-exact
    (2 / 13 / 104 pairs at levels 5 / 6 / 7). They are why the ARITHMETIC MEAN over
    pairs below tol_exact is about 1e-6 (3.0e-6, 1.7e-6, 4.4e-6) while the MEDIAN over
    the same pairs is about 1e-15. Neither number alone supports or refutes
    exactness: use machine_exact_* together with near_miss_count.
"""
import numpy as np
from scipy.optimize import linear_sum_assignment

from .sg_laplacian import sierpinski_graph


EXCEPTIONAL_VALUES = (2.0, 5.0, 6.0)


def dense_spectrum(level):
    """Sorted eigenvalues of the combinatorial graph Laplacian at the
    given level from a dense floating-point solver (numpy.linalg.eigvalsh;
    numerical, not exact arithmetic). Duplicated here, rather than
    imported from spectral_convergence, to keep this module
    self-contained and independently auditable."""
    V, E, _ = sierpinski_graph(level)
    n = len(V)
    L = np.zeros((n, n))
    deg = np.zeros(n)
    for a, b in E:
        L[a, b] = -1
        L[b, a] = -1
        deg[a] += 1
        deg[b] += 1
    for i in range(n):
        L[i, i] = deg[i]
    return np.sort(np.linalg.eigvalsh(L))


def phi(x):
    """Decimation polynomial: maps a level-m eigenvalue down to the
    level-(m-1) eigenvalue it decimates to."""
    return x * (5 - x)


def phi_inverse(mu):
    """The two preimages of mu under phi, i.e. the roots of
    x^2 - 5x + mu = 0. Returns None if no real preimage exists."""
    disc = 25 - 4 * mu
    if disc < 0:
        return None
    r = np.sqrt(disc)
    return ((5 - r) / 2, (5 + r) / 2)


def is_exceptional(v, values=EXCEPTIONAL_VALUES, tol=1e-6):
    return any(abs(v - e) < tol for e in values)


# Classification tolerance for "matched" pairs (historical default; wide) and the tolerance
# below which a pair is called machine-exact. At levels 5-7 the machine-exact residuals are all
# <= 5.2e-14 and the next residual is >= 3.6e-7, so 1e-10 lies inside that gap (measured, see
# the module docstring); it is not a guarantee for higher levels.
TOL_MATCHED_DEFAULT = 1e-4
TOL_MACHINE_DEFAULT = 1e-10


def summarize_residuals(residuals, tol_matched=TOL_MATCHED_DEFAULT,
                        tol_machine=TOL_MACHINE_DEFAULT):
    """Summary statistics of matching residuals, with explicit subsets.

    residuals : 1-D array of nonnegative finite matching residuals |target - eigenvalue|.
    Subsets (every key states which one it refers to):
      matched_*        pairs with residual <  tol_matched  (classification, NOT an exactness claim)
      machine_exact_*  pairs with residual <  tol_machine  (machine precision)
      near_miss_count  pairs with tol_machine <= residual < tol_matched (matched but not exact)
    Statistics are true arithmetic mean, median and max of the stated subset, or NaN when the
    subset is empty. machine_exact_rate is machine_exact_count / len(residuals).
    """
    for name, tol in (("tol_matched", tol_matched), ("tol_machine", tol_machine)):
        if not np.isfinite(tol) or tol <= 0:
            raise ValueError(f"{name} must be finite and positive")
    if tol_machine > tol_matched:
        raise ValueError("tol_machine must not exceed tol_matched")
    r = np.asarray(residuals, dtype=float)
    if r.ndim != 1:
        raise ValueError("residuals must be one-dimensional")
    if not np.all(np.isfinite(r)):
        raise ValueError("residuals must all be finite")
    if np.any(r < 0):
        raise ValueError("residuals must be nonnegative")
    matched = r[r < tol_matched]
    exact = r[r < tol_machine]

    def stat(fn, a):
        return float(fn(a)) if a.size else float("nan")

    return {
        "matched_count": int(matched.size),
        "matched_mean_residual": stat(np.mean, matched),
        "matched_median_residual": stat(np.median, matched),
        "matched_max_residual": stat(np.max, matched),
        "machine_exact_count": int(exact.size),
        "machine_exact_rate": float(exact.size / r.size) if r.size else float("nan"),
        "machine_exact_mean_residual": stat(np.mean, exact),
        "machine_exact_max_residual": stat(np.max, exact),
        "near_miss_count": int(matched.size - exact.size),
    }


def decimation_match_stats(level, exclude_exceptional=True, tol_exact=TOL_MATCHED_DEFAULT,
                           tol_machine=TOL_MACHINE_DEFAULT):
    """Runs the full pipeline for one (level-1, level) pair: builds
    both spectra, forms the 2x preimage targets from level-1, and does
    an optimal one-to-one (Hungarian) match against the level
    spectrum. Returns a dict of diagnostic statistics -- no single
    number here should be read as "the theorem is confirmed/refuted";
    read match_rate alongside n_excluded and the level trend.

    Key semantics (all residuals are |target - assigned eigenvalue| after the
    one-to-one assignment):
      mean_residual, median_residual, max_residual
          over ALL assigned pairs (dominated by unmatched pairs at low levels).
      match_rate_1e-4, match_rate_1e-8
          fraction of pairs with residual < 1e-4 and < 1e-8 (thresholds as named).
      matched_*   statistics over pairs with residual < tol_exact (a broad
          classification threshold; it admits near-misses, so it is NOT an
          exactness claim). matched_mean_residual is the arithmetic mean,
          matched_median_residual the median.
      machine_exact_*   count, rate, mean and max over pairs with residual < tol_machine.
      near_miss_count   pairs with tol_machine <= residual < tol_exact.
      exact_subset_mean_residual
          DEPRECATED alias of matched_mean_residual. Before this change the key
          held the median, not the mean, and its subset was the pairs below
          tol_exact rather than machine-exact pairs; prefer matched_* /
          machine_exact_*.
    """
    lo = dense_spectrum(level - 1)
    lo_nz = np.sort(lo[lo > 1e-8])
    hi = dense_spectrum(level)
    hi_nz = np.sort(hi[hi > 1e-8])

    if exclude_exceptional:
        lo_mask = ~np.array([is_exceptional(v) for v in lo_nz])
        hi_mask = ~np.array([is_exceptional(v) for v in hi_nz])
        n_lo_excluded = int((~lo_mask).sum())
        n_hi_excluded = int((~hi_mask).sum())
        lo_nz = lo_nz[lo_mask]
        hi_nz = hi_nz[hi_mask]
    else:
        n_lo_excluded = n_hi_excluded = 0

    targets = []
    for mu in lo_nz:
        pre = phi_inverse(mu)
        if pre is not None:
            targets.extend(pre)
    targets = np.array(sorted(targets))
    if exclude_exceptional and len(targets) > 0:
        t_mask = ~np.array([is_exceptional(v) for v in targets])
        targets = targets[t_mask]

    cost = np.abs(targets[:, None] - hi_nz[None, :])
    row_ind, col_ind = linear_sum_assignment(cost)
    residuals = cost[row_ind, col_ind]
    summary = summarize_residuals(residuals, tol_exact, tol_machine)

    return {
        "level": level,
        "n_lo": len(lo_nz),
        "n_hi": len(hi_nz),
        "n_targets": len(targets),
        "n_lo_excluded": n_lo_excluded,
        "n_hi_excluded": n_hi_excluded,
        "match_rate_1e-4": float(np.mean(residuals < 1e-4)),
        "match_rate_1e-8": float(np.mean(residuals < 1e-8)),
        "mean_residual": float(residuals.mean()),
        "median_residual": float(np.median(residuals)),
        "max_residual": float(residuals.max()),
        **summary,
        "exact_subset_mean_residual": summary["matched_mean_residual"],
    }
