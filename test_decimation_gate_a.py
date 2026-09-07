"""Nightly test: Gate A rigorous decimation check.

Replaces the question "should we trust the weak `decimation_ratio`
sanity check?" with actual numbers from a proper one-to-one match
between predicted preimages (via phi_inverse) and real level-m
eigenvalues, at levels expensive enough (6, 7) that this does not
belong in the fast per-push suite.

This test is diagnostic, not a pass/fail claim about whether the
theorem "holds" -- see phi_genesis.decimation_check module docstring
for why match_rate < 100% here is expected (recursively-growing
exceptional set), not a refutation of Fukushima-Shima. What IS
asserted:
  - wherever a match is found, it is essentially exact (machine
    precision) -- this WOULD fail if the decimation polynomial were
    wrong, or if the graph construction were inconsistent between
    levels.
  - the match rate increases with level, as theory predicts (shrinking
    relative share of the exceptional set). A decreasing or flat trend
    would indicate something is actually wrong, not just "not yet
    fully characterized".
"""
import pytest

from phi_genesis.decimation_check import decimation_match_stats

pytestmark = pytest.mark.nightly

LEVELS = (5, 6, 7)


def test_decimation_exact_where_matched():
    """Wherever the Hungarian matching finds a pair, the residual
    should be at machine precision -- confirming the decimation
    polynomial phi(x) = x*(5-x) itself is exactly right, independent
    of the open question of exactly which eigenvalues are exceptional."""
    print("\n[Gate A] exactness of matched decimation pairs:")
    for level in LEVELS:
        stats = decimation_match_stats(level)
        print(f"  level {level}: n_lo={stats['n_lo']} n_hi={stats['n_hi']} "
              f"excluded(lo/hi)=({stats['n_lo_excluded']}/{stats['n_hi_excluded']}) "
              f"match_rate(<1e-4)={100*stats['match_rate_1e-4']:.1f}% "
              f"exact_subset_mean_residual={stats['exact_subset_mean_residual']:.2e}")
        # Among pairs ALREADY classified as matched (residual < 1e-4),
        # the mean residual should be at machine precision. This is
        # the real content of the theorem -- if this ever fails, the
        # decimation polynomial or the graph construction is broken,
        # which is a much more serious problem than the match-RATE
        # question tested separately below (match rate is expected to
        # be well under 100% at low levels; exactness of the matches
        # that DO occur is not).
        assert stats["exact_subset_mean_residual"] < 1e-6, (
            f"level {level}: mean residual among matched pairs "
            f"{stats['exact_subset_mean_residual']:.2e} is NOT machine "
            f"precision -- the decimation polynomial or graph "
            f"construction may be broken (this would be a real "
            f"regression, unlike the known open match-rate question)."
        )


def test_decimation_match_rate_increases_with_level():
    """The fraction of eigenvalues explained by the simple {2,5,6}
    exceptional-value exclusion should INCREASE with level (the true
    exceptional set is recursively generated and its relative share of
    the spectrum should shrink as the spectrum grows). A flat or
    decreasing trend would mean the 'recursively shrinking exceptional
    set' explanation is wrong and something else is going on."""
    rates = []
    for level in LEVELS:
        stats = decimation_match_stats(level)
        rates.append(stats["match_rate_1e-4"])

    print(f"\n[Gate A] match-rate trend across levels {LEVELS}: "
          f"{[round(100*r,1) for r in rates]}%")
    print("  Expected: monotonically increasing (shrinking exceptional-set "
          "share). This does NOT confirm Gate A is closed -- the full "
          "recursive exceptional set is still uncharacterized -- but a "
          "non-increasing trend would mean the working explanation is wrong.")

    assert rates == sorted(rates), (
        f"match rate did not increase monotonically across levels {LEVELS}: "
        f"{rates} -- the 'recursively shrinking exceptional set' hypothesis "
        f"may be wrong, this needs human review, not just re-running."
    )
