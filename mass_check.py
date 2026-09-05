"""Honest bridge between the computed SG spectrum and fermion masses.

What the real spectrum gives:  eigenvalues lambda_n with
    lambda_n ~ n^{1/d_s},  1/d_s = ln 5 / (2 ln 3) ~ 0.7565
and a log-periodic fine structure of period ln 5.

What it does NOT give: any reason to identify the index n with
m_experimental / A.  The spectrum is infinite and index labels are
ambiguous under the decimation rescaling, so for ANY target mass there
always exists an index reproducing it.  A mass formula m = A * n is
therefore unfalsifiable as stated; to become a prediction it needs an
independent SELECTION RULE deriving n_f from boundary conditions.

This module performs the only honest quantitative comparison available:
  - compute A implied by each fermion if n is the eigenvalue index
  - test whether a single scale A is consistent (it is not, absent a
    selection rule -- shown here explicitly)
"""
import numpy as np

PHI = (1 + np.sqrt(5)) / 2
V_EV = 246220.0          # MeV
ALPHA = 1 / 137.035999084

EXPERIMENTAL = {
    "mu": 105.6583745,
    "tau": 1776.86,
    "charm": 1275.0,
    "bottom": 4180.0,
    "top": 173100.0,
}

FITTED_N = {  # the hardcoded values from the old repo (kept for the audit)
    "mu": 1.0196, "tau": 17.146, "charm": 12.303, "bottom": 40.335,
    "top": 1680.0,
}


def a_from_formula():
    """A = v * alpha / Phi^6 -- the v8.7 derivation."""
    return V_EV * ALPHA / PHI**6


def implied_scales():
    """Scale A implied per fermion: A_f = m_exp / n_fitted."""
    return {f: EXPERIMENTAL[f] / FITTED_N[f] for f in EXPERIMENTAL}


def scale_consistency():
    """Relative spread of implied scales. Zero spread would mean ONE scale."""
    A = np.array(list(implied_scales().values()))
    return float((A.max() - A.min()) / A.mean())
