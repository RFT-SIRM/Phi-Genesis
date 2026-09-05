import numpy as np
from phi_genesis.mobius import mobius_spectrum, gap_selected_indices
from phi_genesis.sg_laplacian import graph_laplacian_spectrum

def test_mobius_gaps_the_spectrum():
    """pi-flux through all holes must remove all near-zero modes."""
    plain = graph_laplacian_spectrum(4)
    mob = mobius_spectrum(4)
    assert mob[0] > 10 * plain[plain > 1e-8][0]

def test_gap_selection_not_particles():
    """The lacunary gap structure 3^k-1 does not select {1,12,17,40}."""
    sel = gap_selected_indices(graph_laplacian_spectrum(5), k=8)
    assert set(sel).isdisjoint({12, 17, 40})

def test_integer_rounding_quality():
    """Integer n with one scale beats fitted decimals (0.68% vs 0.87%)."""
    A = 104.63
    err = np.mean([abs(A*1-105.6583745)/105.6583745,
                   abs(A*17-1776.86)/1776.86,
                   abs(A*12-1275.0)/1275.0,
                   abs(A*40-4180.0)/4180.0]) * 100
    assert err < 0.87
