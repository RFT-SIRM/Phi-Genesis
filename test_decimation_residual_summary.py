"""Fast unit tests for the residual statistics of phi_genesis.decimation_check.

They pin the semantics of every reported statistic (arithmetic mean vs median, matched vs
machine-exact subsets) on synthetic data, so a mean can never again be computed with a median.
"""
import math

import numpy as np
import pytest

from phi_genesis import decimation_check as check
from phi_genesis.decimation_check import summarize_residuals


def test_mean_and_median_are_distinct_statistics_of_the_matched_subset():
    r = np.array([1e-15, 2e-15, 8e-5, 2e-4])            # last one is not matched (>= 1e-4)
    out = summarize_residuals(r, tol_matched=1e-4, tol_machine=1e-10)
    matched = r[:3]
    assert out["matched_count"] == 3
    assert out["matched_mean_residual"] == pytest.approx(float(np.mean(matched)), rel=1e-12)
    assert out["matched_median_residual"] == pytest.approx(2e-15, rel=1e-12)
    assert out["matched_max_residual"] == pytest.approx(8e-5, rel=1e-12)
    assert out["matched_mean_residual"] > 1e-5 > out["matched_median_residual"]


def test_machine_exact_and_near_miss_subsets():
    r = np.array([1e-15, 2e-15, 3e-12, 5e-8, 8e-5, 2e-4])
    out = summarize_residuals(r, tol_matched=1e-4, tol_machine=1e-10)
    assert out["machine_exact_count"] == 3
    assert out["machine_exact_rate"] == pytest.approx(3 / 6)
    assert out["machine_exact_mean_residual"] == pytest.approx((1e-15 + 2e-15 + 3e-12) / 3, rel=1e-12)
    assert out["machine_exact_max_residual"] == pytest.approx(3e-12, rel=1e-12)
    assert out["matched_count"] == 5
    assert out["near_miss_count"] == 2                  # 5e-8 and 8e-5


def test_threshold_is_strict_inequality():
    # 1e-4 is not < tol_matched (excluded); 1e-10 is < tol_matched but not < tol_machine
    out = summarize_residuals([1e-4, 1e-10], tol_matched=1e-4, tol_machine=1e-10)
    assert out["matched_count"] == 1
    assert out["machine_exact_count"] == 0
    assert out["near_miss_count"] == 1


def test_empty_subsets_are_nan_not_zero():
    out = summarize_residuals([1e-3, 2e-3], tol_matched=1e-4, tol_machine=1e-10)
    assert out["matched_count"] == 0 and out["machine_exact_count"] == 0
    assert out["near_miss_count"] == 0
    for key in ("matched_mean_residual", "matched_median_residual", "matched_max_residual",
                "machine_exact_mean_residual", "machine_exact_max_residual"):
        assert math.isnan(out[key]), key
    assert out["machine_exact_rate"] == 0.0
    assert math.isnan(summarize_residuals([])["machine_exact_rate"])


@pytest.mark.parametrize("tol_matched, tol_machine", [
    (0.0, 1e-10), (-1.0, 1e-10), (math.inf, 1e-10), (math.nan, 1e-10),
    (1e-4, 0.0), (1e-4, math.nan), (1e-10, 1e-4),        # last: tol_machine > tol_matched
])
def test_invalid_tolerances_rejected(tol_matched, tol_machine):
    with pytest.raises(ValueError):
        summarize_residuals([1e-15], tol_matched, tol_machine)


@pytest.mark.parametrize("bad", [[-1.0], [math.inf], [math.nan], [[1e-9]]])
def test_invalid_residuals_rejected(bad):
    with pytest.raises(ValueError):
        summarize_residuals(bad)


def test_decimation_match_stats_reports_all_semantics(monkeypatch):
    """End to end through decimation_match_stats on a tiny synthetic spectrum whose preimage
    targets are well separated, so the Hungarian assignment is unambiguous."""
    low = np.array([0.0, 1.0, 1.5])
    targets = sorted(v for mu in low[1:] for v in check.phi_inverse(mu))
    offsets = np.array([1e-15, 3e-5, 8e-5, 2e-4])
    high_nz = np.array([t + d for t, d in zip(targets, offsets)])
    high = np.r_[0.0, high_nz]
    monkeypatch.setattr(check, "dense_spectrum", lambda level: low if level == 0 else high)

    s = check.decimation_match_stats(1, exclude_exceptional=True, tol_exact=1e-4, tol_machine=1e-10)

    residuals = np.abs(np.array(targets) - high_nz)      # float residuals actually assigned
    matched = residuals[residuals < 1e-4]
    assert s["n_targets"] == 4
    assert s["matched_count"] == 3 and s["near_miss_count"] == 2
    assert s["machine_exact_count"] == 1
    assert s["matched_mean_residual"] == pytest.approx(float(np.mean(matched)), rel=1e-9)
    assert s["matched_median_residual"] == pytest.approx(float(np.median(matched)), rel=1e-9)
    assert s["matched_mean_residual"] != s["matched_median_residual"]
    # deprecated alias: arithmetic mean over the matched subset (it used to hold the median)
    assert s["exact_subset_mean_residual"] == s["matched_mean_residual"]
    assert s["match_rate_1e-4"] == pytest.approx(3 / 4)
    assert s["mean_residual"] == pytest.approx(float(residuals.mean()), rel=1e-9)
    assert s["median_residual"] == pytest.approx(float(np.median(residuals)), rel=1e-9)
