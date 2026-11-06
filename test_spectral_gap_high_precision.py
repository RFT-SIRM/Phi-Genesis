"""Regression tests for the high-precision local-face spectral calculation.

These checks deliberately exercise the three-dimensional low spectral cluster:
the level-5 bottom eigenvalue is separated from the next two modes by only
about 2e-18, so a single-vector float64 inverse iteration is not sufficient.
The tolerances below check numerical reproducibility, not a formal certificate.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import pytest

SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "high_precision_bottom.py"
)
SPEC = importlib.util.spec_from_file_location("high_precision_bottom", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load high-precision script at {SCRIPT}")
high_precision_bottom = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(high_precision_bottom)


@pytest.mark.parametrize(
    ("level", "expected"),
    [
        (2, "1.29843788128357565675589116268909336773979477"),
        (3, "1.30907106525560684040369338452482482532600235"),
        (4, "1.30912891862700323733722692655076172660493747"),
        (5, "1.30912892028081342053762494641145938300147538"),
    ],
)
def test_high_precision_bottom_eigenvalue_reproduces(level, expected):
    result = high_precision_bottom.high_precision_low_cluster(level)
    assert abs(result["eigenvalues"][0] - mp.mpf(expected)) < mp.mpf("1e-30")
    assert result["block_residual"] < mp.mpf("1e-19")
    assert max(result["eigen_residuals"]) < mp.mpf("1e-19")


def test_level_five_low_cluster_is_resolved_not_collapsed_to_one_value():
    result = high_precision_bottom.high_precision_low_cluster(5)
    bottom, second, third = result["eigenvalues"]

    # The latter two modes are numerically degenerate; the lowest mode is
    # distinct, but the splitting is below ordinary float64 resolution.
    splitting = second - bottom
    assert mp.mpf("1.5e-18") < splitting < mp.mpf("2.5e-18")
    assert abs(third - second) < mp.mpf("1e-30")


SYMMETRY_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "symmetry_sector_bottom.py"
)
SYMMETRY_SPEC = importlib.util.spec_from_file_location(
    "symmetry_sector_bottom", SYMMETRY_SCRIPT
)
if SYMMETRY_SPEC is None or SYMMETRY_SPEC.loader is None:
    raise ImportError(f"cannot load symmetry-sector script at {SYMMETRY_SCRIPT}")
symmetry_sector_bottom = importlib.util.module_from_spec(SYMMETRY_SPEC)
SYMMETRY_SPEC.loader.exec_module(symmetry_sector_bottom)


@pytest.mark.parametrize("level", [3, 4, 5, 6])
def test_alternating_a2_sector_bottom_is_two(level):
    result = symmetry_sector_bottom.a2_bottom(level, iterations=40)
    assert abs(result["lambda"] - mp.mpf("2")) < mp.mpf("1e-25")
    assert result["residual"] < mp.mpf("1e-25")



def test_level_six_a1_sector_bottom():
    result = symmetry_sector_bottom.a1_bottom(6, iterations=60)
    expected = mp.mpf(
        "1.309128920280813421888623088170810187650767803108018768"
    )
    assert result["sector_dimension"] == 186
    assert abs(result["lambda"] - expected) < mp.mpf("1e-35")
    assert result["residual"] < mp.mpf("1e-40")


def test_level_six_e_sector_near_degenerate_mode():
    result = symmetry_sector_bottom.e_sector_bottom(6, iterations=15)
    expected = mp.mpf(
        "1.309128920280813421888623088170810189003102475121980131"
    )
    assert result["sector_dimension"] == 365
    assert abs(result["lambda"] - expected) < mp.mpf("1e-30")
    assert result["residual"] < mp.mpf("1e-20")
