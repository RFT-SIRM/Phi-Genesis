"""Nightly deep tests -- expensive, exploratory, NOT run on every push.

Why these are separate from the fast suite (test_honest.py, test_mobius.py,
test_fukushima_shima.py, test_convergence_and_selection.py):
those finish in ~2 minutes total and gate every commit/PR. The tests here
either need hours of wall-clock/GBs of RAM, or thousands of Monte-Carlo
trials -- expensive on every push, but exactly the kind of thing you want
running once a day and archived in the log.

Selected and run only via the `nightly` pytest marker, by
.github/workflows/nightly-deep-tests.yml (cron, 00:00 UTC daily,
355-minute timeout). Excluded from the fast CI job via `-m "not nightly"`.

Two tests, matching two open items from the external audits (GPT + Kimi):

  1. test_level9_dense_eigensolve_attempt  -- Roadmap item "Level 9+ via
     sparse optimization or GPU" / Open Problem #2. Pushes the EXACT dense
     eigendecomposition to level 9 (29,526 vertices) and records whatever
     happens (success, MemoryError, or timeout) as data. It is not allowed
     to assert that level 9 converges -- that would not be honest yet.

  2. test_gate_e_statistical_null_sweep -- Gate E from the audits: "how
     likely is 0.68% mean error by pure chance with an unconstrained
     integer search?" Answered as a SWEEP over the assumed prior range for
     n (the audits didn't specify one, so pretending there's a single
     right answer would hide a real methodological choice), not a single
     p-value. See the printed table for the actual sensitivity.
"""
import signal
import time

import numpy as np
import pytest

from phi_genesis import sierpinski_graph
from phi_genesis.spectral_convergence import (
    dense_laplacian_spectrum, naive_weyl_fit, THEORY_EXPONENT,
)
from phi_genesis.mass_check import EXPERIMENTAL

pytestmark = pytest.mark.nightly

LEVEL = 9
LEVEL9_VERTEX_COUNT = (3 ** (LEVEL + 1) + 3) // 2  # closed form N_m = (3^(m+1)+3)/2


class _Timeout(Exception):
    pass


def _alarm(signum, frame):
    raise _Timeout()


def test_level9_graph_construction_is_feasible():
    """Floor check: building the level-9 GRAPH (vertices+edges, no
    eigensolve) is O(vertices) memory, so it should always succeed. If
    this fails, something regressed in sierpinski_graph() itself --
    unrelated to whether the eigensolve scales."""
    t0 = time.time()
    V, E, _ = sierpinski_graph(LEVEL)
    dt = time.time() - t0
    print(f"\n[level {LEVEL}] vertices={len(V)} edges={len(E)} "
          f"(expected {LEVEL9_VERTEX_COUNT} vertices), built in {dt:.1f}s")
    assert len(V) == LEVEL9_VERTEX_COUNT


def test_level9_dense_eigensolve_attempt(max_seconds=3 * 3600):
    """Attempt the full dense eigendecomposition at level 9
    (~29,526 x 29,526 real symmetric matrix, ~6.5 GB for the matrix
    alone in float64, before eigh()'s own working memory).

    This is a DATA-COLLECTION test, not a physics claim: it records
    whether the runner's RAM/time budget is enough, and if not, which
    limit was hit. Either outcome is printed to the nightly log so
    Open Problem #2's status is visible without anyone re-running it
    by hand on their own machine.
    """
    signal.signal(signal.SIGALRM, _alarm)
    signal.alarm(max_seconds)
    t0 = time.time()
    try:
        spec = dense_laplacian_spectrum(LEVEL)
        dt = time.time() - t0
        naive = naive_weyl_fit(spec)
        err = 100 * abs(naive - THEORY_EXPONENT) / THEORY_EXPONENT
        print(f"\n[level {LEVEL}] SUCCEEDED in {dt:.0f}s. "
              f"naive Weyl exponent={naive:.4f} "
              f"(theory={THEORY_EXPONENT:.4f}, err={err:.2f}%)")
    except MemoryError:
        print(f"\n[level {LEVEL}] MemoryError after {time.time() - t0:.0f}s -- "
              f"runner RAM insufficient for a "
              f"{LEVEL9_VERTEX_COUNT}x{LEVEL9_VERTEX_COUNT} dense eigh(). "
              f"Expected failure mode until Open Problem #2 (sparse/GPU "
              f"level-9+ solver) is actually solved.")
    except _Timeout:
        print(f"\n[level {LEVEL}] Timed out after {max_seconds}s without "
              f"finishing. Same conclusion as MemoryError: dense eigh() "
              f"does not scale to level {LEVEL} on a standard CI runner.")
    finally:
        signal.alarm(0)
    # Intentionally no assertion on the numeric outcome of (a) -- only
    # that the attempt was made and its result was captured, whatever
    # that result is.
    assert True


def test_gate_e_statistical_null_sweep(n_samples=20_000_000, seed=0):
    """Gate E (external audit): quantify the look-elsewhere effect
    behind the reported 0.68% mean error for {n_mu, n_tau, n_c, n_b} =
    {1, 12, 17, 40}.

    For several assumed search ranges n in [1, n_max], draw n_samples
    random integer quadruples, fit a single scale A = mean(m_i/n_i) to
    each quadruple (mirroring implied_scales() in mass_check.py), and
    measure what fraction of random quadruples reach a mean relative
    error <= 0.68% purely by chance.

    We sweep n_max instead of picking one, because the audits did not
    specify a prior range for n, and the answer changes qualitatively
    with it (verified by hand: p ~ 0 for n_max <= 500, p > 0 once
    n_max reaches the scale of the top-quark index, ~1680-2000). Any
    single number would silently bake in a choice nobody actually
    argued for.
    """
    masses = np.array([
        EXPERIMENTAL["mu"], EXPERIMENTAL["tau"],
        EXPERIMENTAL["charm"], EXPERIMENTAL["bottom"],
    ])
    reported_mean_err = 0.68  # %, README section 4 (4-fermion integer fit)

    print(f"\n[Gate E] {n_samples:,} random quadruples per n_max, "
          f"target <= {reported_mean_err}% mean error:")
    print(f"{'n_max':>8s} {'hits':>10s} {'p_hat':>12s} {'min_err%':>10s}")

    results = {}
    for n_max in (50, 100, 500, 1000, 2000, 5000):
        rng = np.random.default_rng(seed)
        ns = rng.integers(1, n_max + 1, size=(n_samples, 4))
        implied_A = masses[None, :] / ns
        A_best = implied_A.mean(axis=1, keepdims=True)
        rel_err_pct = 100 * np.abs(A_best * ns - masses[None, :]) / masses[None, :]
        mean_err_pct = rel_err_pct.mean(axis=1)

        hits = int((mean_err_pct <= reported_mean_err).sum())
        p_hat = hits / n_samples
        results[n_max] = p_hat
        print(f"{n_max:8d} {hits:10d} {p_hat:12.7f} {mean_err_pct.min():10.3f}")

    # Purely informational: assert the sweep ran and produced valid
    # probabilities, not any specific physics conclusion about which
    # n_max is "the right one" -- that is a modeling choice, not a fact
    # this test can settle.
    assert all(0.0 <= p <= 1.0 for p in results.values())
