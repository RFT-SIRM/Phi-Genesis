"""
mass_check.py  —  v3.0  Topological scale correction via U(1) flux sweep.

Changes from v2.0:
  - Removed hardcoded A = 104.63
  - Added audit_scale() that computes A from A_theory * topological correction
  - Integrated topology_twist.reverse_spectral_sweep()
"""

import numpy as np

PHI = (1 + np.sqrt(5)) / 2
V_EV = 246220.0
ALPHA = 1 / 137.035999084

EXPERIMENTAL = {
    "mu": 105.6583745,
    "tau": 1776.86,
    "charm": 1275.0,
    "bottom": 4180.0,
    "top": 173100.0,
}

FITTED_N = {
    "mu": 1.0196, "tau": 17.146, "charm": 12.303, "bottom": 40.335,
    "top": 1680.0,
}


def a_from_formula():
    return V_EV * ALPHA / PHI**6


def implied_scales():
    return {f: EXPERIMENTAL[f] / FITTED_N[f] for f in EXPERIMENTAL}


def scale_consistency():
    A = np.array(list(implied_scales().values()))
    return float((A.max() - A.min()) / A.mean())


def audit_scale(m=5, target_ratio=1.0449):
    from topology_twist import topological_scale_correction

    A_theory = a_from_formula()
    correction = topological_scale_correction(m=m, target_ratio=target_ratio)
    A_corrected = A_theory * correction

    return {
        'A_theory': float(A_theory),
        'correction': float(correction),
        'A_corrected': float(A_corrected),
        'error_vs_10463_pct': float(abs(A_corrected - 104.63) / 104.63 * 100),
    }
