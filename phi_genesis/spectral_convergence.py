"""Weyl-exponent convergence analysis on the Sierpinski gasket.

Combines:
  * Dense eigensolver (exact, tractable to level 8)
  * Naive fixed-window fit (parameter-free, honest baseline)
  * Phase-averaged sliding-window estimator (one candidate correction)
  * Full sensitivity sweep (demonstrates instability of window choice)

HONEST STATUS:
  - Naive fit converges slowly: 4.1% (level 5) -> 2.8% (level 8)
  - Phase-averaged can dip below 1% at some levels/window choices,
    but the result is NOT stable against window-parameter variation.
  - No robust, parameter-free finite-level correction is known.
  - Open Problem #2: find a convergent estimator of d_s/2 from
    pre-fractal spectra.
"""
import numpy as np
from .sg_laplacian import sierpinski_graph

THEORY_EXPONENT = np.log(3) / np.log(5)
LN5 = np.log(5)


def dense_laplacian_spectrum(level):
    """Full graph-Laplacian spectrum via dense eigh (exact; tractable
    to level ~8, unlike sparse ARPACK 'SM' mode for near-complete spectra)."""
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


def naive_weyl_fit(spectrum, lo=1e-4, hi=0.5):
    """Fixed-window log-log fit. The only parameter-free estimator here."""
    nz = spectrum[spectrum > 1e-8]
    N = np.arange(1, len(nz) + 1)
    mask = (nz > lo) & (nz < hi)
    return np.polyfit(np.log(nz[mask]), np.log(N[mask]), 1)[0]


def weyl_exponent_phase_averaged(level=6, lam_min=1e-4, lam_max=0.5,
                                  n_periods=3, step=0.1):
    """Sliding-window slope averaged over windows of width n_periods*ln(5).

    NOTE: this is ONE point in an unstable family of estimators.
    See window_choice_sensitivity() for the full spread."""
    spec = graph_laplacian_spectrum(level)
    nz = spec[spec > 1e-8]
    N = np.arange(1, len(nz) + 1)
    ln_lam, ln_N = np.log(nz), np.log(N)
    mask = (nz > lam_min) & (nz < lam_max)
    W = n_periods * LN5
    lo, hi = ln_lam[mask].min(), ln_lam[mask].max()
    slopes = []
    for s in np.arange(lo, hi - W, step):
        m2 = (ln_lam >= s) & (ln_lam <= s + W)
        if m2.sum() > 20:
            slopes.append(np.polyfit(ln_lam[m2], ln_N[m2], 1)[0])
    return float(np.mean(slopes)) if slopes else float("nan")


def sliding_window_slope(spectrum, k=3, step_frac=0.1, margin=0.1):
    """Mean log-log slope over sliding windows of width k*ln(5)."""
    nz = spectrum[spectrum > 1e-8]
    N = np.arange(1, len(nz) + 1)
    lnl = np.log(nz)
    lnN = np.log(N)
    width = k * LN5
    start = lnl.min() + margin
    slopes = []
    while start + width < lnl.max() - margin:
        m = (lnl >= start) & (lnl <= start + width)
        if m.sum() > 5:
            slopes.append(np.polyfit(lnl[m], lnN[m], 1)[0])
        start += step_frac * LN5
    slopes = np.array(slopes)
    if len(slopes) == 0:
        return float("nan"), float("nan"), 0
    return float(slopes.mean()), float(slopes.std()), len(slopes)


def nonoverlapping_window_slope(spectrum, k=3, margin=0.1):
    """Mean slope over NON-overlapping windows of width k*ln(5)."""
    nz = spectrum[spectrum > 1e-8]
    N = np.arange(1, len(nz) + 1)
    lnl = np.log(nz)
    lnN = np.log(N)
    width = k * LN5
    start = lnl.min() + margin
    slopes = []
    while start + width < lnl.max():
        m = (lnl >= start) & (lnl <= start + width)
        if m.sum() > 5:
            slopes.append(np.polyfit(lnl[m], lnN[m], 1)[0])
        start += width
    slopes = np.array(slopes)
    if len(slopes) == 0:
        return float("nan"), float("nan"), 0
    return float(slopes.mean()), float(slopes.std()), len(slopes)


def window_choice_sensitivity(spectrum, ks=(1, 2, 3, 4, 5), steps=(0.05, 0.1, 0.2, 0.5)):
    """Sweep window-averaging parameters and report spread.
    Demonstrates that phase-averaging is NOT a unique correction."""
    rows = []
    for k in ks:
        for step in steps:
            m, s, n = sliding_window_slope(spectrum, k=k, step_frac=step)
            if n > 0:
                rows.append({"method": "sliding", "k": k, "step": step,
                             "exponent": m, "err_pct": 100 * abs(m - THEORY_EXPONENT) / THEORY_EXPONENT,
                             "n_windows": n})
        m, s, n = nonoverlapping_window_slope(spectrum, k=k)
        if n > 0:
            rows.append({"method": "non_overlapping", "k": k, "step": None,
                         "exponent": m, "err_pct": 100 * abs(m - THEORY_EXPONENT) / THEORY_EXPONENT,
                         "n_windows": n})
    return rows


def convergence_table():
    """Table of naive fit + range of window-averaged estimates."""
    theory = THEORY_EXPONENT
    rows = []
    for lev in [5, 6, 7, 8]:
        spec = dense_laplacian_spectrum(lev)
        naive = naive_weyl_fit(spec)
        sens = window_choice_sensitivity(spec)
        errs = [r["err_pct"] for r in sens]
        rows.append({
            "level": lev,
            "vertices": len(spec),
            "naive_exponent": naive,
            "naive_err_pct": 100 * abs(naive - theory) / theory,
            "window_err_min_pct": min(errs) if errs else None,
            "window_err_max_pct": max(errs) if errs else None,
            "n_methods": len(sens),
        })
    return rows
