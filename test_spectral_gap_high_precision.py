"""Regression tests for the high-precision local-face spectral calculation.

These checks deliberately exercise the three-dimensional low spectral cluster:
the level-5 bottom eigenvalue is separated from the next two modes by only
about 2e-18, so a single-vector float64 inverse iteration is not sufficient.
The tolerances below check numerical reproducibility, not a formal certificate.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path

import mpmath as mp
import numpy as np
import pytest

SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "high_precision_bottom.py"
)
SPEC = importlib.util.spec_from_file_location("high_precision_bottom", SCRIPT)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load high-precision script at {SCRIPT}")
high_precision_bottom = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(high_precision_bottom)


@pytest.mark.parametrize(
    ("level", "expected"),
    [
        (2, "1.29843788128357565675589116268909336773979477"),
        (3, "1.30907106525560684040369338452482482532600235"),
        (4, "1.30912891862700323733722692655076172660493747"),
        (5, "1.30912892028081342053762494641145938300147538"),
    ],
)
def test_high_precision_bottom_eigenvalue_reproduces(level, expected):
    result = high_precision_bottom.high_precision_low_cluster(level)
    assert abs(result["eigenvalues"][0] - mp.mpf(expected)) < mp.mpf("1e-30")
    assert result["block_residual"] < mp.mpf("1e-19")
    assert max(result["eigen_residuals"]) < mp.mpf("1e-19")


def test_level_five_low_cluster_is_resolved_not_collapsed_to_one_value():
    result = high_precision_bottom.high_precision_low_cluster(5)
    bottom, second, third = result["eigenvalues"]

    # The latter two modes are numerically degenerate; the lowest mode is
    # distinct, but the splitting is below ordinary float64 resolution.
    splitting = second - bottom
    assert mp.mpf("1.5e-18") < splitting < mp.mpf("2.5e-18")
    assert abs(third - second) < mp.mpf("1e-30")


SYMMETRY_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "symmetry_sector_bottom.py"
)
SYMMETRY_SPEC = importlib.util.spec_from_file_location(
    "symmetry_sector_bottom", SYMMETRY_SCRIPT
)
if SYMMETRY_SPEC is None or SYMMETRY_SPEC.loader is None:
    raise ImportError(f"cannot load symmetry-sector script at {SYMMETRY_SCRIPT}")
symmetry_sector_bottom = importlib.util.module_from_spec(SYMMETRY_SPEC)
SYMMETRY_SPEC.loader.exec_module(symmetry_sector_bottom)


@pytest.mark.parametrize("level", [3, 4, 5, 6])
def test_alternating_a2_sector_bottom_is_two(level):
    result = symmetry_sector_bottom.a2_bottom(level, iterations=40)
    assert abs(result["lambda"] - mp.mpf("2")) < mp.mpf("1e-25")
    assert result["residual"] < mp.mpf("1e-25")



def test_level_six_a1_sector_bottom():
    result = symmetry_sector_bottom.a1_bottom(6, iterations=60)
    expected = mp.mpf(
        "1.309128920280813421888623088170810187650767803108018768"
    )
    assert result["sector_dimension"] == 186
    assert abs(result["lambda"] - expected) < mp.mpf("1e-35")
    assert result["residual"] < mp.mpf("1e-40")


def test_level_six_e_sector_near_degenerate_mode():
    result = symmetry_sector_bottom.e_sector_bottom(6, iterations=15)
    expected = mp.mpf(
        "1.309128920280813421888623088170810189003102475121980131"
    )
    assert result["sector_dimension"] == 365
    assert abs(result["lambda"] - expected) < mp.mpf("1e-30")
    assert result["residual"] < mp.mpf("1e-20")



@pytest.mark.parametrize("level", [2, 3, 4, 5])
def test_s3_irreducible_sector_spectra_reconstruct_full_graph(level):
    """The A1, A2, and two conjugate E sectors exhaust the full spectrum."""
    (
        a1_shifted,
        a1_float,
        full_graph,
        full_dimension,
        a1_dimension,
    ) = symmetry_sector_bottom.build_a1_quotient(level)
    (
        a2_shifted,
        a2_float,
        a2_full_dimension,
        a2_dimension,
    ) = symmetry_sector_bottom.build_a2_quotient(level)
    (
        _e_rows,
        _e_diagonal,
        e_float,
        _e_full_graph,
        e_full_dimension,
        e_dimension,
    ) = symmetry_sector_bottom.build_e_sector(level)

    assert a2_full_dimension == full_dimension
    assert e_full_dimension == full_dimension
    assert a1_dimension + a2_dimension + 2 * e_dimension == full_dimension

    a1_spectrum = np.linalg.eigvalsh(a1_float + np.eye(a1_dimension))
    a2_spectrum = np.linalg.eigvalsh(a2_float + np.eye(a2_dimension))
    e_spectrum = np.linalg.eigvalsh(e_float.toarray())
    sector_union = np.sort(
        np.concatenate([a1_spectrum, a2_spectrum, e_spectrum, e_spectrum])
    )
    full_spectrum = np.linalg.eigvalsh(full_graph.toarray())

    # Independent dense diagonalizations are compared with a tolerance
    # comfortably above the observed float64 roundoff (<= 1.2e-14).
    assert sector_union.shape == full_spectrum.shape
    assert np.max(np.abs(sector_union - full_spectrum)) < 5e-12


@pytest.mark.parametrize(
    ("sector", "expected", "dimension"),
    [
        (
            "A1",
            "1.309128920280813421888623088170810187650767803108018768",
            186,
        ),
        (
            "E",
            "1.309128920280813421888623088170810189003102475121980131",
            365,
        ),
    ],
)
def test_mixed_precision_refinement_reproduces_level_six_bottom(
    sector, expected, dimension
):
    result = symmetry_sector_bottom.mixed_precision_bottom(
        6, sector, iterations=110, dps=75
    )
    assert result["sector_dimension"] == dimension
    assert abs(result["lambda"] - mp.mpf(expected)) < mp.mpf("1e-35")
    assert result["residual"] < mp.mpf("1e-55")
    assert result["linear_residual"] < mp.mpf("1e-55")


@pytest.mark.parametrize("level", [2, 3, 4, 5])
def test_sparse_a1_quotient_matches_dense_reference(level):
    dense_mp, dense_float, full_graph, full_dimension, sector_dimension = (
        symmetry_sector_bottom.build_a1_quotient(level)
    )
    rows, sparse_float, sparse_graph, sparse_full, sparse_dimension, asymmetry = (
        symmetry_sector_bottom.build_a1_quotient_sparse(level)
    )

    assert sparse_full == full_dimension
    assert sparse_dimension == sector_dimension
    assert (sparse_graph != full_graph).nnz == 0
    assert asymmetry < mp.mpf("1e-60")
    assert np.max(np.abs(sparse_float.toarray() - dense_float)) < 1e-14
    for i, row in enumerate(rows):
        for j, value in row:
            assert abs(value - dense_mp[i, j]) < mp.mpf("1e-60")
