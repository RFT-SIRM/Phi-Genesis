"""Tests for the exact A1/E boundary Schur-complement recursion."""
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
SCHUR_SPEC = importlib.util.spec_from_file_location("schur_decimation_for_test", SCHUR_SCRIPT)
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
    vertices, index, _neighbors, _degree, Q = symmetry_sector_bottom.build_graph(level)
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
def test_forward_derivatives_match_mpmath_diff(level):
    with mp.workdps(100):
        point = mp.mpf("1.234")
        a1_value, a1_derivative = (
            schur_decimation.a1_characteristic_with_derivative(point, level)
        )
        a1_expected = mp.diff(
            lambda x: schur_decimation.a1_characteristic(x, level), point
        )
        e_value, e_derivative = (
            schur_decimation.e_characteristic_with_derivative(point, level)
        )
        e_expected = mp.diff(
            lambda x: schur_decimation.e_characteristic(x, level), point
        )
        assert abs(
            a1_value - schur_decimation.a1_characteristic(point, level)
        ) < mp.mpf("1e-90")
        assert abs(
            e_value - schur_decimation.e_characteristic(point, level)
        ) < mp.mpf("1e-90")
        assert abs(a1_derivative - a1_expected) < mp.mpf("1e-85")
        assert abs(e_derivative - e_expected) < mp.mpf("1e-85")


def test_level_twelve_a1_boundary_root_and_quadratic_increment():
    roots = schur_decimation.a1_boundary_root_sequence(12, dps=1250)
    with mp.workdps(1250):
        expected_prefix = mp.mpf(
            "1.3091289202808134218886230881708101885523242511173263434335359844526816974043999830777949027911712"
        )
        assert abs(roots[12] - expected_prefix) < mp.mpf("1e-90")
        increments = {level: roots[level] - roots[level - 1] for level in range(2, 13)}
        assert mp.mpf("1.15e-1163") < increments[12] < mp.mpf("1.17e-1163")
        ratio = increments[12] / increments[11] ** 2
        expected_ratio = mp.mpf("0.4939504899001989528562882796535409482107481")
        assert abs(ratio - expected_ratio) < mp.mpf("1e-35")


def test_level_eleven_e_a1_boundary_splitting():
    a1_roots = schur_decimation.a1_boundary_root_sequence(11, dps=1250)
    e_roots = schur_decimation.e_boundary_root_sequence(11, dps=1250)
    with mp.workdps(1250):
        splitting_9 = e_roots[9] - a1_roots[9]
        delta_9 = a1_roots[9] - a1_roots[8]
        assert mp.mpf("4.69e-291") < splitting_9 < mp.mpf("4.71e-291")
        ratio_9 = splitting_9 / delta_9**2
        splitting_11 = e_roots[11] - a1_roots[11]
        delta_11 = a1_roots[11] - a1_roots[10]
        assert mp.mpf("1.73e-1163") < splitting_11 < mp.mpf("1.75e-1163")
        ratio_11 = splitting_11 / delta_11**2
        expected = mp.mpf("0.74092573485029842928443241948031142231612216498")
        assert abs(ratio_9 - expected) < mp.mpf("1e-35")
        assert abs(ratio_11 - expected) < mp.mpf("1e-35")



@pytest.mark.parametrize(
    ("level", "expected", "tol"),
    [
        (
            5,
            "1.30912892028081342256412215905048560442889305924618119065096",
            "1e-50",
        ),
        (
            6,
            "1.30912892028081342188862308817081018900310247512198013098385",
            "1e-55",
        ),
        (
            7,
            "1.30912892028081342188862308817081018855232425111732634343353598445268169760514245722344731949215782007648",
            "1e-80",
        ),
        (
            8,
            "1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341960876021582905006341",
            "1e-140",
        ),
    ],
)
def test_e_boundary_roots_match_independent_matrix_spectrum(level, expected, tol):
    roots = schur_decimation.e_boundary_root_sequence(level, dps=220)
    with mp.workdps(220):
        assert abs(roots[level] - mp.mpf(expected)) < mp.mpf(tol)


def test_e_a1_shift_ratio_converges_to_three_halves():
    a1_roots = schur_decimation.a1_boundary_root_sequence(12, dps=2450)
    e_roots = schur_decimation.e_boundary_root_sequence(11, dps=2450)
    expected_decimal_orders = {
        7: 70,
        8: 143,
        9: 288,
        10: 578,
        11: 1160,
    }
    with mp.workdps(2450):
        for level, decimal_order in expected_decimal_orders.items():
            next_a1_increment = a1_roots[level + 1] - a1_roots[level]
            ratio = (e_roots[level] - a1_roots[level]) / next_a1_increment
            assert abs(ratio - mp.mpf("1.5")) < mp.power(10, -decimal_order)




@pytest.mark.parametrize("level", range(13))
@pytest.mark.parametrize("point", ["1.234", "1.309", "1.411"])
def test_a1_derivative_obeys_differentiated_schur_update(level, point):
    """Check the derivative of f_(m+1)=f_m-2*b_m*(c+5b)/(c+3b)."""
    with mp.workdps(100):
        x = mp.mpf(point)
        a, b, da, db = schur_decimation._schur_parameters_with_derivative(x, level)
        c = 2 * a + x - b
        dc = 2 * da + 1 - db
        denominator = c + 3 * b
        ratio = (c + 5 * b) / denominator
        ratio_derivative = 2 * (c * db - b * dc) / denominator**2

        predicted = (da + 2 * db) - 2 * db * ratio - 2 * b * ratio_derivative
        actual = schur_decimation.a1_characteristic_with_derivative(x, level + 1)[1]
        assert abs(actual - predicted) < mp.mpf("1e-85")

def test_insufficient_precision_does_not_repeat_a_boundary_root():
    with pytest.raises(ArithmeticError, match="cannot resolve"):
        schur_decimation.a1_boundary_root_sequence(10, dps=100)
    with pytest.raises(ArithmeticError, match="cannot resolve"):
        schur_decimation.e_boundary_root_sequence(10, dps=100)
