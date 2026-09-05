import numpy as np
from phi_genesis.spectral_convergence import (
    dense_laplacian_spectrum, naive_weyl_fit, window_choice_sensitivity,
    THEORY_EXPONENT,
)
from phi_genesis.mobius_selection_search import (
    exhaustive_twist_search, search_summary, TARGET_INDICES,
)


def test_dense_solver_matches_sparse_at_level_6():
    """Dense eigh must agree with sparse eigsh path."""
    from phi_genesis.sg_laplacian import graph_laplacian_spectrum
    sparse = np.sort(graph_laplacian_spectrum(6))
    dense = np.sort(dense_laplacian_spectrum(6))
    k = len(sparse)
    assert np.allclose(sparse, dense[:k], atol=1e-4)


def test_naive_fit_stays_above_one_percent_at_level_8():
    """Parameter-free naive fit does NOT reach <1% even at 9843 vertices."""
    spec = dense_laplacian_spectrum(8)
    naive = naive_weyl_fit(spec)
    err_pct = 100 * abs(naive - THEORY_EXPONENT) / THEORY_EXPONENT
    assert err_pct > 1.0


def test_window_averaging_is_not_a_stable_correction():
    """Sweeping window choices produces a wide spread of estimates."""
    spec = dense_laplacian_spectrum(6)
    sens = window_choice_sensitivity(spec)
    errs = [r["err_pct"] for r in sens]
    assert len(sens) > 10
    assert min(errs) < 1.0
    assert max(errs) > 10.0


def test_no_generation_twist_selects_all_four_targets():
    """None of 32 generation-twist configs selects all of {1,12,17,40}."""
    results = exhaustive_twist_search(level=5)
    assert len(results) == 32
    s = search_summary(results)
    assert s["max_simultaneous_hits"] < len(TARGET_INDICES)


def test_forty_never_selected_by_generation_twists():
    """Index 40 never appears as gap-selected under any config."""
    results = exhaustive_twist_search(level=5)
    s = search_summary(results)
    assert not s["index_40_ever_selected"]
