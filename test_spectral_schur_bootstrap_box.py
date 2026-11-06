"""Regression test for the finite A1 Schur bootstrap-window experiment."""
from __future__ import annotations

import importlib.util
from pathlib import Path
import sys

SCRIPT = (Path(__file__).parent / "computational" / "spectral_gap_theta_2pi" / "schur_bootstrap_box_iv.py")
SPEC = importlib.util.spec_from_file_location("schur_bootstrap_box_iv_for_test", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load bootstrap experiment from {SCRIPT}")
bootstrap = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = bootstrap
SPEC.loader.exec_module(bootstrap)


def test_level_six_window_brackets_a1_roots_and_bootstraps_through_101():
    from mpmath import mp
    result = bootstrap.certify_bootstrap(max_level=101, dps=180, radius_digits=140)
    assert mp.mpf(result["level6_left_f"]) > 0
    assert mp.mpf(result["level6_right_f"]) < 0
    assert mp.mpf(result["final_left_f"]) > 0
    assert mp.mpf(result["final_right_f"]) < 0
    assert mp.mpf(result["min_pivot_lower"]) > mp.mpf("1.30")
    assert mp.mpf(result["max_contraction_upper"]) < mp.mpf("0.764")
    assert mp.mpf(result["conditional_root_shift_bound"]) < mp.mpf("1.1e-36")
    assert result["max_level"] == 101
    assert result["snapshots"][-1][0] == 101
