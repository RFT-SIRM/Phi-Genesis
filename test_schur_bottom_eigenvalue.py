"""Regression checks for the standalone high-precision Schur-root calculation."""
from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import pytest


ROOT = Path(__file__).parent
SCRIPT = ROOT / "computational" / "spectral_gap_theta_2pi" / "schur_bottom_eigenvalue.py"
SPEC = importlib.util.spec_from_file_location("schur_bottom_eigenvalue_test", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load Schur-root script at {SCRIPT}")
schur_bottom = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(schur_bottom)

DECIMATION_SCRIPT = (
    ROOT / "computational" / "spectral_gap_theta_2pi" / "schur_decimation.py"
)
DECIMATION_SPEC = importlib.util.spec_from_file_location(
    "schur_decimation_for_standalone_test", DECIMATION_SCRIPT
)
if DECIMATION_SPEC is None or DECIMATION_SPEC.loader is None:
    raise ImportError(f"cannot load Schur decimation at {DECIMATION_SCRIPT}")
schur_decimation = importlib.util.module_from_spec(DECIMATION_SPEC)
DECIMATION_SPEC.loader.exec_module(schur_decimation)


@pytest.mark.parametrize("level", [0, 1, 3, 6, 9, 12])
@pytest.mark.parametrize("lam", ["1.234", "1.309", "1.411"])
def test_standalone_boundary_convention_matches_ordinary_schur(level, lam):
    """T_m = S_m + lambda I: off-diagonal agrees, diagonal shifts by lambda."""
    with mp.workdps(90):
        spectral_parameter = mp.mpf(lam)
        alpha, beta = schur_bottom.T(level, spectral_parameter)
        a, b = schur_decimation.schur_parameters(spectral_parameter, level)
        assert abs((alpha - spectral_parameter) - a) < mp.mpf("1e-78")
        assert abs(beta - b) < mp.mpf("1e-78")


def test_standalone_reported_a1_roots_and_increment_ratio():
    a1, e = schur_bottom.compute_roots(a1_max_level=9, e_max_level=7, dps=260)
    with mp.workdps(240):
        expected_9 = mp.mpf(
            "1.3091289202808134218886230881708101885523242511173263434335359844526816974043999830777949027911712"
        )
        assert abs(a1[9] - expected_9) < mp.mpf("1e-95")
        increments = {m: a1[m] - a1[m - 1] for m in range(4, 10)}
        ratio_9 = increments[9] / increments[8] ** 2
        expected_ratio = mp.mpf(
            "0.493950489900198952856288279653540948210748109987"
        )
        assert abs(ratio_9 - expected_ratio) < mp.mpf("1e-45")
        assert set(e) == set(range(3, 8))


def test_standalone_e_splitting_is_resolved_through_level_seven():
    a1, e = schur_bottom.compute_roots(a1_max_level=9, e_max_level=7, dps=260)
    with mp.workdps(240):
        expected = {
            4: "2.4807153e-9",
            5: "2.0264972e-18",
            6: "1.3523347e-36",
            7: "6.022274224369572501029599e-73",
        }
        for level, value in expected.items():
            splitting = e[level] - a1[level]
            assert splitting > 0
            assert abs(splitting - mp.mpf(value)) < mp.mpf(value) * mp.mpf("5e-8")


def test_standalone_root_request_rejects_e_level_beyond_a1_sequence():
    with pytest.raises(ValueError, match="e_max_level"):
        schur_bottom.compute_roots(a1_max_level=7, e_max_level=8, dps=260)
