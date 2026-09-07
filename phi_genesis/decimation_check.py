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

HONEST RESULT (see test_decimation_gate_a.py for the numbers):
  - Wherever a match IS found, the residual is at machine precision
    (~1e-15) -- the polynomial relation is exact, not approximate.
  - The MATCH RATE is well below 100% at low levels (level 5: ~38%,
    level 6: ~57%) even after excluding the three classically known
    exceptional values {2, 5, 6}.
  - The match rate increases with level, consistent with theory: the
    true exceptional set is NOT just {2, 5, 6} -- it is a recursively
    generated family (preimages of exceptional values are themselves
    exceptional), so its size grows with level while its RELATIVE
    share of the spectrum shrinks. This module implements the simple
    (non-recursive) exclusion only; full recursive characterization of
    the exceptional set remains OPEN (Gate A: mechanism identified,
    not fully closed).
"""
import numpy as np
from scipy.optimize import linear_sum_assignment

from .sg_laplacian import sierpinski_graph


EXCEPTIONAL_VALUES = (2.0, 5.0, 6.0)


def dense_spectrum(level):
    """Exact dense eigendecomposition of the combinatorial graph
    Laplacian at the given level (duplicated here, rather than
    imported from spectral_convergence, to keep this module
    self-contained and independently auditable)."""
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


def decimation_match_stats(level, exclude_exceptional=True, tol_exact=1e-4):
    """Runs the full pipeline for one (level-1, level) pair: builds
    both spectra, forms the 2x preimage targets from level-1, and does
    an optimal one-to-one (Hungarian) match against the level
    spectrum. Returns a dict of diagnostic statistics -- no single
    number here should be read as "the theorem is confirmed/refuted";
    read match_rate alongside n_excluded and the level trend.
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

    return {
        "level": level,
        "n_lo": len(lo_nz),
        "n_hi": len(hi_nz),
        "n_targets": len(targets),
        "n_lo_excluded": n_lo_excluded,
        "n_hi_excluded": n_hi_excluded,
        "match_rate_1e-4": float(np.mean(residuals < tol_exact)),
        "match_rate_1e-8": float(np.mean(residuals < 1e-8)),
        "mean_residual": float(residuals.mean()),
        "median_residual": float(np.median(residuals)),
        "max_residual": float(residuals.max()),
        # Mean residual restricted to pairs already classified as
        # "matched" (residual < tol_exact) -- this is the right
        # quantity to check machine-precision exactness, since at low
        # levels the match rate itself is well under 50% and the raw
        # median/mean over ALL pairs is dominated by genuinely
        # unmatched (exceptional) eigenvalues, not by imprecision.
        "exact_subset_mean_residual": (
            float(np.median(residuals[residuals < tol_exact]))
            if np.any(residuals < tol_exact) else float("nan")
        ),
    }
