"""Tests for the exact A1 boundary Schur-complement recursion."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import numpy as np
import pytest

SCHUR_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "schur_decimation.py"
)
SCHUR_SPEC = importlib.util.spec_from_file_location(
    "schur_decimation_for_test", SCHUR_SCRIPT
)
if SCHUR_SPEC is None or SCHUR_SPEC.loader is None:
    raise ImportError(f"cannot load Schur-decimation script at {SCHUR_SCRIPT}")
schur_decimation = importlib.util.module_from_spec(SCHUR_SPEC)
SCHUR_SPEC.loader.exec_module(schur_decimation)

SYMMETRY_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "symmetry_sector_bottom.py"
)
SYMMETRY_SPEC = importlib.util.spec_from_file_location(
    "symmetry_sector_bottom_for_schur_test", SYMMETRY_SCRIPT
)
if SYMMETRY_SPEC is None or SYMMETRY_SPEC.loader is None:
    raise ImportError(f"cannot load symmetry-sector script at {SYMMETRY_SCRIPT}")
symmetry_sector_bottom = importlib.util.module_from_spec(SYMMETRY_SPEC)
SYMMETRY_SPEC.loader.exec_module(symmetry_sector_bottom)


@pytest.mark.parametrize("level", range(5))
@pytest.mark.parametrize("lam", ["1.234", "1.309", "1.411"])
def test_recursion_matches_direct_boundary_schur_complement(level, lam):
    vertices, index, _neighbors, _degree, Q = (
        symmetry_sector_bottom.build_graph(level)
    )
    side = 1 << level
    boundary = [index[p] for p in ((0, 0), (side, 0), (0, side))]
    interior = [i for i in range(len(vertices)) if i not in boundary]
    dense = Q.toarray()
    matrix = dense - float(lam) * np.eye(len(vertices))
    if interior:
        direct = (
            matrix[np.ix_(boundary, boundary)]
            - matrix[np.ix_(boundary, interior)]
            @ np.linalg.solve(
                matrix[np.ix_(interior, interior)],
                matrix[np.ix_(interior, boundary)],
            )
        )
    else:
        direct = matrix[np.ix_(boundary, boundary)]

    with mp.workdps(80):
        a, b = schur_decimation.schur_parameters(mp.mpf(lam), level)
        predicted = np.full((3, 3), float(b))
        np.fill_diagonal(predicted, float(a))
    assert np.max(np.abs(direct - predicted)) < 5e-12


@pytest.mark.parametrize("level", range(7))
def test_forward_derivative_matches_mpmath_diff(level):
    with mp.workdps(100):
        point = mp.mpf("1.234")
        value, derivative = (
            schur_decimation.a1_characteristic_with_derivative(point, level)
        )
        expected = mp.diff(
            lambda x: schur_decimation.a1_characteristic(x, level),
            point,
        )
        assert abs(
            value - schur_decimation.a1_characteristic(point, level)
        ) < mp.mpf("1e-90")
        assert abs(derivative - expected) < mp.mpf("1e-85")


def test_level_twelve_a1_boundary_root_and_quadratic_increment():
    roots = schur_decimation.a1_boundary_root_sequence(12, dps=1250)
    with mp.workdps(1250):
        expected_prefix = mp.mpf(
            "1.3091289202808134218886230881708101885523242511173263434335359844526816974043999830777949027911712"
        )
        assert abs(roots[12] - expected_prefix) < mp.mpf("1e-90")
        increments = {
            level: roots[level] - roots[level - 1]
            for level in range(2, 13)
        }
        assert mp.mpf("1.15e-1163") < increments[12] < mp.mpf("1.17e-1163")
        ratio = increments[12] / increments[11] ** 2
        expected_ratio = mp.mpf(
            "0.4939504899001989528562882796535409482107481"
        )
        assert abs(ratio - expected_ratio) < mp.mpf("1e-35")


def test_insufficient_precision_does_not_repeat_an_old_root():
    import pytest
    with pytest.raises(ArithmeticError, match="cannot resolve"):
        schur_decimation.a1_boundary_root_sequence(10, dps=100)
