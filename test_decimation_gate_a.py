"""Nightly test: Gate A rigorous decimation check.

Replaces the question "should we trust the weak `decimation_ratio`
sanity check?" with actual numbers from a proper one-to-one match
between predicted preimages (via phi_inverse) and real level-m
eigenvalues, at levels expensive enough (6, 7) that this does not
belong in the fast per-push suite.

This test is diagnostic, not a pass/fail claim about whether the
theorem "holds" -- see phi_genesis.decimation_check module docstring
for why a machine-exact rate < 100% here is expected (recursively-growing
exceptional set and/or the corner-degree-2 boundary of this Laplacian),
not a refutation of Fukushima-Shima. What IS asserted:
  - the pairs classified as machine-exact (residual < tol_machine) really
    are at machine precision: their largest residual is far below the
    classification tolerance. This WOULD fail if the decimation polynomial
    were wrong, or if the graph construction were inconsistent between
    levels.
  - the match rate increases with level, as theory predicts (shrinking
    relative share of the exceptional set), both for the broad 1e-4 rate and
    for the machine-exact rate. A decreasing or flat trend would indicate
    something is actually wrong, not just "not yet fully characterized".

What is deliberately NOT asserted: that the arithmetic mean over all pairs
below the broad tolerance 1e-4 is at machine precision. It is not (about 1e-6,
because "near-miss" pairs with residual 1e-7..1e-4 pass the broad tolerance
without being exact), and a median over that subset must not be used to hide
this. Success on part of the spectrum is not evidence of a full spectral
correspondence.
"""
from functools import lru_cache

import pytest

from phi_genesis.decimation_check import decimation_match_stats

pytestmark = pytest.mark.nightly

LEVELS = (5, 6, 7)

# Measured at levels 5-7 (largest machine-exact residual: 1.2e-14, 2.0e-14, 5.2e-14). The bound
# 1e-11 leaves a margin of more than two orders of magnitude for platform differences in LAPACK,
# and is a factor 10 below the classification tolerance tol_machine = 1e-10, so the assertion is
# not satisfied by construction.
MACHINE_EXACT_MAX_RESIDUAL = 1e-11


@lru_cache(maxsize=None)
def _stats(level):
    return decimation_match_stats(level)


def test_decimation_exact_where_matched():
    """Pairs classified as machine-exact have residuals at machine precision --
    confirming the decimation polynomial phi(x) = x*(5-x) is exactly right for
    those eigenvalues, independent of the open question of which eigenvalues
    are exceptional."""
    print("\n[Gate A] matched decimation pairs (matched = residual < 1e-4, "
          "machine-exact = residual < 1e-10):")
    for level in LEVELS:
        s = _stats(level)
        print(f"  level {level}: n_targets={s['n_targets']} "
              f"matched={s['matched_count']} (mean {s['matched_mean_residual']:.2e}, "
              f"median {s['matched_median_residual']:.2e}, max {s['matched_max_residual']:.2e}) "
              f"machine_exact={s['machine_exact_count']} ({100*s['machine_exact_rate']:.1f}%, "
              f"max {s['machine_exact_max_residual']:.2e}) near_miss={s['near_miss_count']}")
        assert s["machine_exact_count"] > 0, (
            f"level {level}: no pair is machine-exact -- the decimation polynomial or graph "
            f"construction may be broken (a real regression, unlike the known open "
            f"exact-rate question).")
        # The assertion concerns pairs already classified as exact. The matched-subset mean
        # (matched_mean_residual) is printed but not asserted: near-miss pairs make it ~1e-6
        # at every level here, which says nothing about imprecision of the exact pairs.
        assert s["machine_exact_max_residual"] < MACHINE_EXACT_MAX_RESIDUAL, (
            f"level {level}: largest residual among machine-exact pairs "
            f"{s['machine_exact_max_residual']:.2e} is not below "
            f"{MACHINE_EXACT_MAX_RESIDUAL:.0e} -- the decimation polynomial or graph "
            f"construction may be broken (this would be a real regression).")


def test_decimation_match_rate_increases_with_level():
    """The fraction of eigenvalues explained by the simple {2,5,6}
    exceptional-value exclusion should INCREASE with level (the true
    exceptional set is recursively generated and its relative share of
    the spectrum should shrink as the spectrum grows). A flat or
    decreasing trend would mean the 'recursively shrinking exceptional
    set' explanation is wrong and something else is going on."""
    rates_matched = [_stats(level)["match_rate_1e-4"] for level in LEVELS]
    rates_exact = [_stats(level)["machine_exact_rate"] for level in LEVELS]

    print(f"\n[Gate A] rate trend across levels {LEVELS}: "
          f"match<1e-4 {[round(100*r, 1) for r in rates_matched]}%, "
          f"machine-exact {[round(100*r, 1) for r in rates_exact]}%")
    print("  Expected: monotonically increasing (shrinking exceptional-set "
          "share). This does NOT confirm Gate A is closed -- the full "
          "recursive exceptional set is still uncharacterized -- but a "
          "non-increasing trend would mean the working explanation is wrong.")

    assert rates_matched == sorted(rates_matched), (
        f"match rate (<1e-4) did not increase monotonically across levels {LEVELS}: "
        f"{rates_matched} -- the 'recursively shrinking exceptional set' hypothesis "
        f"may be wrong, this needs human review, not just re-running.")
    assert rates_exact == sorted(rates_exact), (
        f"machine-exact rate did not increase monotonically across levels {LEVELS}: "
        f"{rates_exact} -- the 'recursively shrinking exceptional set' hypothesis "
        f"may be wrong, this needs human review, not just re-running.")
