"""Code-correctness tests for the pre-registered protocol (PREREGISTRATION.md v1.0).
They use synthetic inputs only and do NOT evaluate the real family against the targets."""
import numpy as np

from phi_genesis import selection_protocol as sp
from phi_genesis.sg_index_triviality import gap_selected_indices as repo_rule


def test_rule_matches_repo_triviality_rule():
    rng = np.random.default_rng(0)
    for _ in range(20):
        spec = np.sort(np.abs(rng.normal(size=200)) + 1e-3)
        assert list(sp.select(spec)) == repo_rule(spec, k=12, window=60)


def test_graph_invariants():
    coords, E, A, C = sp.graph()
    assert len(coords) == 366 and len(C) == 3 and A.sum() == 2 * len(E)


def test_family_has_75_unique_configs():
    fam = sp.family()
    assert len(fam) == 75 == 48 + 7 + 20
    assert len({lab for lab, _ in fam}) == 75


def test_dirichlet_and_circle_shapes():
    fam = dict(sp.family())
    n = len(sp.graph()[0])
    assert len(fam["F2:dirichlet(0,)"]) == n - 1
    assert len(fam["F2:dirichlet(0, 185, 365)"]) == n - 3
    assert len(fam["F3:N=8,phi=0.25"]) == 8 * n
    assert abs(fam["F3:N=3,phi=0"][0]) < 1e-9                  # phi = 0 keeps the zero mode


def test_null_pool_is_deterministic():
    a = sp.generate_pool("N-edge", 6, seed=1)
    b = sp.generate_pool("N-edge", 6, seed=1)
    assert a == b and all(len(s) == sp.K for s in a)


def test_score_and_weights():
    rates = {i: 0.5 for i in range(1, sp.WINDOW)}
    w = sp.weights(rates)
    assert abs(sp.score((1, 12, 40, 7), w) - 3 * np.log(2)) < 1e-12
    assert sp.score((2, 3), w) == 0.0


def test_max_pvalue_limits():
    ns = np.zeros(100)
    assert sp.max_pvalue(ns, 0.0, M=75, B=500, seed=1) == 1.0       # observed = null max: no evidence
    assert sp.max_pvalue(ns, 1.0, M=75, B=500, seed=1) == 1 / 501   # above every null max


def test_pipeline_runs_on_tiny_pool(tmp_path):
    """Smoke test only: tiny pools, results meaningless by construction."""
    sp.step_a(out_dir=str(tmp_path), pool_size=40)
    old = sp.BOOTSTRAP_B
    sp.BOOTSTRAP_B = 50
    try:
        sp.step_b(out_dir=str(tmp_path))
    finally:
        sp.BOOTSTRAP_B = old
    assert (tmp_path / "results_v1.json").exists()
