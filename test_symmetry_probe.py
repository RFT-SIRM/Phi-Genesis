"""Regression tests for the exploratory D3 representation audit."""

import pytest

from phi_genesis.sg_laplacian import sierpinski_graph
from phi_genesis.symmetry_probe import d3_vertex_permutations, symmetry_probe


LEVELS = (5, 6, 7)
TARGET_EXPECTATIONS = {
    1: (1, 2, 2, 0, 0, 1),
    12: (12, 14, 3, 1, 0, 1),
    17: (16, 17, 2, 0, 0, 1),
    40: (30, 41, 12, 3, 1, 4),
}
EXPECTED_SIMPLE_A1 = (3, 9, 18, 27, 48, 54)


@pytest.fixture(scope="module")
def audits():
    return {level: symmetry_probe(level) for level in LEVELS}


def test_six_barycentric_d3_actions_are_graph_automorphisms():
    for level in LEVELS:
        vertices, edges, _ = sierpinski_graph(level)
        actions = d3_vertex_permutations(vertices, edges, level)
        assert len(actions) == 6
        assert all(sorted(action.tolist()) == list(range(len(vertices))) for action in actions)


def test_cluster_signature_is_stable_across_levels_five_six_seven(audits):
    reference = audits[5].signature()
    assert audits[6].signature() == reference
    assert audits[7].signature() == reference


def test_targets_use_one_based_positive_spectrum_ranks(audits):
    # Rank 1 is not the constant zero mode: it belongs to the first positive E doublet.
    for level in LEVELS:
        audit = audits[level]
        for rank, expected in TARGET_EXPECTATIONS.items():
            cluster = audit.cluster_containing(rank)
            actual = (
                cluster.start,
                cluster.end,
                cluster.multiplicity,
                cluster.a1,
                cluster.a2,
                cluster.e_multiplicity,
            )
            assert actual == expected


def test_simple_fully_symmetric_a1_ranks_in_first_sixty(audits):
    for audit in audits.values():
        assert audit.simple_a1_ranks() == EXPECTED_SIMPLE_A1

LEVEL_EIGENVALUES = {
    5: {1: 0.005741958474563, 12: 0.143567179457051, 17: 0.200112150540496, 40: 0.697224362268003},
    6: {1: 0.001154094053506, 12: 0.028880249655440, 17: 0.040496798530680, 40: 0.143567179457049},
    7: {1: 0.000231192288259, 12: 0.005782737942710, 17: 0.008122335554676, 40: 0.028880249655436},
}


def test_reported_target_eigenvalues_match_at_all_three_levels(audits):
    for level, target_values in LEVEL_EIGENVALUES.items():
        for rank, expected in target_values.items():
            cluster = audits[level].cluster_containing(rank)
            assert cluster.eigenvalue == pytest.approx(expected, rel=1e-9, abs=1e-12)
