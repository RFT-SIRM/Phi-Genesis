import numpy as np
from phi_genesis import (graph_laplacian_spectrum, spectral_dimension_check,
                         decimation_ratio, spectral_asymmetry, CLAIMED_POTENTIAL,
                         a_from_formula, implied_scales, scale_consistency, PHI)

def test_decimation_factor_5():
    r = decimation_ratio(6)
    assert abs(r[:4].mean() - 5.0) < 0.05

def test_weyl_exponent():
    fit, theory = spectral_dimension_check(6)
    assert abs(fit - theory) < 0.05

def test_eta_claim_fails():
    a = spectral_asymmetry(4, CLAIMED_POTENTIAL)
    assert abs(a) <= 4 and a != -4

def test_a_formula_discrepancy_is_real():
    assert abs(a_from_formula() - 103.63) / 103.63 > 0.03

def test_no_single_scale():
    assert scale_consistency() > 0.001
