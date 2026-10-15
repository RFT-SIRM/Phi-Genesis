"""Tests for numerical inertia counting on the SG Laplacian and for the (verified, small-level)
multiplicity structure of its special eigenvalues. Fast tests run in CI; the window-sweep
data collection is nightly and, per this repo's policy, asserts only sanity -- never that a
particular estimator has converged."""
import numpy as np
import pytest

from phi_genesis.sg_inertia import (sparse_laplacian, count_below, counting_function,
                                    window_slopes, THEORY_EXPONENT)


def _dense_spectrum(level):
    L, _ = sparse_laplacian(level)
    return np.sort(np.linalg.eigvalsh(L.toarray()))


def test_inertia_matches_dense_levels_5_and_6():
    sig = [0.003, 0.02, 0.1, 0.5, 1.3, 2.7, 3.3, 4.2, 5.6]   # none is an eigenvalue
    for level in (5, 6):
        L, _ = sparse_laplacian(level)
        ev = _dense_spectrum(level)
        for s in sig:
            assert count_below(L, s) == int(np.sum(ev < s)), (level, s)


def _distinct_eigenvalues(ev, tol=1e-8):
    out, i = [], 0
    while i < len(ev):
        j = i
        while j + 1 < len(ev) and abs(ev[j + 1] - ev[i]) < tol:
            j += 1
        out.append(float(ev[i:j + 1].mean()))
        i = j + 1
    return out


def test_inertia_matches_dense_near_every_eigenvalue_levels_5_and_6():
    """Measured reliable regime: sigma = lambda +- delta for every distinct eigenvalue lambda,
    delta = 1e-3 and 1e-6, compared with the dense spectrum. (The count was also correct for
    delta down to 1e-8 at levels 5-7, but not at 1e-9; see the sg_inertia module docstring. The
    tests stay two decades away from that boundary.) This checks a measured regime; it is not a
    proof of correctness of the floating-point factorization."""
    for level in (5, 6):
        L, _ = sparse_laplacian(level)
        ev = _dense_spectrum(level)
        for lam in _distinct_eigenvalues(ev):
            for delta in (1e-3, 1e-6):
                for s in (lam - delta, lam + delta):
                    assert count_below(L, s) == int(np.sum(ev < s)), (level, lam, delta, s)


def test_eigenvalue_sigma_is_rejected():
    L, _ = sparse_laplacian(4)
    with pytest.raises(ValueError):
        count_below(L, 0.0)          # 0 is an eigenvalue (constant vector)


def test_multiplicities_of_special_eigenvalues_levels_3_to_6():
    """Verified numerically for levels 3-7 (levels 3-6 here for speed):
    mult(3) = (3^(m-1)-3)/2, mult(5) = (3^(m-1)-1)/2, mult(6) = (3^m-3)/2.
    An observed pattern checked at five levels, not a proof."""
    for m in range(3, 7):
        ev = _dense_spectrum(m)
        c = lambda v: int(np.sum(np.abs(ev - v) < 1e-7))
        assert c(3.0) == (3 ** (m - 1) - 3) // 2
        assert c(5.0) == (3 ** (m - 1) - 1) // 2
        assert c(6.0) == (3 ** m - 3) // 2


def test_count_is_a_power_of_three_at_sigma_0p003():
    """Observed for levels 6-10: N(0.003) = 3^(level-5) (sigma lies in a spectral gap)."""
    for level in (6, 7, 8):
        L, _ = sparse_laplacian(level)
        assert count_below(L, 0.003) == 3 ** (level - 5)


@pytest.mark.nightly
def test_window_sweep_levels_8_and_9_records_spread_only():
    """DATA COLLECTION. Prints the spread of log-log slopes over window choices. Asserts only
    sanity (finite, monotone counts) -- not convergence to ln3/ln5."""
    sig = 1e-3 * 5 ** (np.arange(0, 61) / 16)
    for level in (8, 9):
        N = counting_function(level, sig)
        assert np.all(np.diff(N) >= 0)
        for k in (1, 2, 3):
            sl = window_slopes(sig, N, k, lo_cut=2e-3, hi_cut=0.45)
            assert len(sl) > 0 and np.all(np.isfinite(sl))
            print(f"\n[level {level}] k={k}: mean {sl.mean():.4f} "
                  f"({100*(sl.mean()-THEORY_EXPONENT)/THEORY_EXPONENT:+.2f}%), "
                  f"range {sl.min():.4f}..{sl.max():.4f}, n={len(sl)}")
