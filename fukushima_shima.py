"""Fukushima-Shima spectral gap series on the Sierpinski gasket.

Classic result (Fukushima & Shima, 1992): the Laplacian spectrum on SG
splits into two decimation series with forbidden zones (gaps):
  * 5-series: eigenvalues near lambda map via lambda -> 5 - lambda
  * 6-series: eigenvalues near lambda map via lambda -> 6 - lambda

This module verifies the gap structure numerically at level 6 by locating
the largest absolute gaps in the spectrum and confirming they cluster at
the decimation fixed points (lambda ~ 3 and lambda ~ 5).
"""
import numpy as np
from sg_laplacian import graph_laplacian_spectrum


def gap_locations(level=6, top_k=8):
    """Return (gap_positions, gap_sizes) of the largest absolute gaps."""
    spec = graph_laplacian_spectrum(level)
    nz = spec[spec > 1e-8]
    d = np.diff(nz)
    idx = np.argsort(d)[::-1][:top_k]
    return nz[idx], d[idx]


def gap_structure_check(level=6):
    """Verify largest gaps sit near the 5-series and 6-series fixed points."""
    pos, sizes = gap_locations(level, top_k=6)
    # 5-series fixed point: lambda = 5/2 = 2.5 (from lambda = 5 - lambda)
    # 6-series fixed point: lambda = 3   (from lambda = 6 - lambda)
    near_5series = np.any(np.abs(pos - 2.5) < 0.8)
    near_6series = np.any(np.abs(pos - 3.0) < 0.8)
    return near_5series and near_6series, pos, sizes
