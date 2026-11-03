"""Fast finite regression tests for the signed-Z2 H10 computation."""
from phi_genesis.higher_moments_z2 import (
    build_generation_flux_problem,
    compute_full_flux_h10,
    compute_generation_twist_traces,
    q_transition,
    signed_laplacian,
    trace_even_power_frobenius,
    trace_power_sequential,
    validate_against_reference,
)


def test_packed_boundary_solver_matches_project_reference_through_level_five():
    report = validate_against_reference(max_level=5, all_generation_masks_at_level=5)
    assert [row["vertices"] for row in report] == [6, 15, 42, 123, 366]
    assert [row["reference_masks_checked"] for row in report] == [2, 4, 8, 16, 32]


def test_full_flux_h10_exact_regression_through_level_five():
    rows = compute_full_flux_h10(max_level=5)
    assert [row["D10"] for row in rows] == [
        19_523_880,
        178_774_440,
        548_852_760,
        1_658_945_640,
        4_989_224_280,
    ]
    assert [row["residual"] for row in rows[1:]] == [
        120_202_800,
        12_529_440,
        12_387_360,
        12_387_360,
    ]


def test_q_transition_exhaustive_for_level_three_to_four():
    level3 = compute_generation_twist_traces(3)
    level4 = compute_generation_twist_traces(4)
    for mask in range(1 << 3):
        a, b, c = ((mask >> j) & 1 for j in range(3))
        for d in (0, 1):
            next_mask = mask | (d << 3)
            assert level4[next_mask] - 3 * level3[mask] == q_transition(a, b, c, d)


def test_frobenius_trace_identity_matches_sequential_sparse_power():
    problem = build_generation_flux_problem(5)
    full_mask = (1 << 5) - 1
    laplacian = signed_laplacian(problem, full_mask)
    assert trace_even_power_frobenius(laplacian, 10) == trace_power_sequential(laplacian, 10)
    assert trace_even_power_frobenius(laplacian, 10) == 12_923_578_938
