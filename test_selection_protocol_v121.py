"""Fast tests for protocol v1.2.1 code. They check mechanics only; none evaluates the family against the targets."""
import numpy as np

from phi_genesis import selection_protocol_v121 as m


def test_family_is_ten_pre_registered_configurations():
    fam = m.family()
    assert len(fam) == 10
    assert sorted({round(R * R, 6) for _, R, _ in fam}) == sorted(round(5.0 ** j, 6) for j in m.J_VALUES)
    assert {phi for _, _, phi in fam} == {0.0, 0.5}


def test_mode_truncation_does_not_change_selection():
    lam = m.plain_lam()
    rng = np.random.default_rng(7)
    small, big = m._N, np.arange(-400, 401, dtype=float)
    for _ in range(25):
        R, phi = 5.0 ** rng.uniform(-2, 2), rng.uniform(0, 1)
        a = m.select_sum(lam, R, phi)
        m._N = big
        b = m.select_sum(lam, R, phi)
        m._N = small
        assert a == b


def test_ratio_rule_invariant_under_monotone_maps():
    """A Dirac operator whose square is the scalar operator gives the same selection (sqrt is monotone)."""
    from phi_genesis import selection_protocol as sp
    rng = np.random.default_rng(3)
    x = np.sort(rng.uniform(0.01, 5, 300))
    assert sp.select(x, k=8, window=60) == sp.select(np.sqrt(x), k=8, window=60)


def test_pipeline_runs_on_decoy_targets_only():
    rng = np.random.default_rng(11)
    pools = {name: [m.DRAWS[name](rng) for _ in range(400)] for name in ("N-circ",)}
    res = m.evaluate(pools, targets=(2, 13, 19, 41), half=200)
    assert res["M"] == 10 and "N-circ" in res["nulls"]
