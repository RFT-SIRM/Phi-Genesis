"""Second-derivative checks for the A1 Schur root-shift analysis."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import pytest

CERTIFICATE_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "schur_derivative_certificate.py"
)
SPEC = importlib.util.spec_from_file_location(
    "schur_derivative_certificate_for_test", CERTIFICATE_SCRIPT
)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load derivative certificate at {CERTIFICATE_SCRIPT}")
derivative_certificate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(derivative_certificate)


@pytest.mark.parametrize("level", range(5, 8))
def test_a1_second_derivative_interval_encloses_mpmath_difference(level):
    interval_context = derivative_certificate.iv
    previous_interval_dps = interval_context.dps
    # Keep the interval enclosure a little wider than the independently
    # rounded 100-digit scalar reference, regardless of earlier tests that
    # may have changed the shared mpmath.iv precision.
    interval_context.dps = 80
    try:
        with mp.workdps(100):
            point = mp.mpf("1.309")
            interval_point = interval_context.mpf(point)
            _a, _b, _da, _db, dda, ddb, _pivots = (
                derivative_certificate._schur_interval_second_order(interval_point, level)
            )
            interval_second = dda + 2 * ddb
            first_derivative = lambda x: derivative_certificate.schur_decimation.a1_characteristic_with_derivative(x, level)[1]
            expected = mp.diff(first_derivative, point)
            lower = mp.make_mpf(interval_second.a._mpi_[0])
            upper = mp.make_mpf(interval_second.b._mpi_[0])
            assert lower <= expected <= upper
    finally:
        interval_context.dps = previous_interval_dps


def test_derivative_transition_certificate_smoke_through_level_seven():
    rows = derivative_certificate.certify_derivative_transitions(
        max_level=7, dps=180, radius_digits=120, start_level=5
    )
    assert len(rows) == 2
    for row in rows:
        assert row["curvature_lower"] > mp.mpf("-0.29")
        assert row["curvature_upper"] < mp.mpf("-0.07")
        assert row["g_ratio_upper"] < mp.mpf("0.7")
        assert row["derivative_variation_ratio_upper"] < 1
        assert row["b_contraction_ratio_upper"] < mp.mpf("0.8")
