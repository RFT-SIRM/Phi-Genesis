"""Finite-level Schur/inertia interval certificates for the bottom spectral cluster."""
from __future__ import annotations

import importlib.util
import sys
from decimal import Decimal
from pathlib import Path

CERTIFICATE_SCRIPT = (
    Path(__file__).parent
    / "computational"
    / "spectral_gap_theta_2pi"
    / "schur_inertia_certificate.py"
)
SPEC = importlib.util.spec_from_file_location(
    "schur_inertia_certificate_for_test", CERTIFICATE_SCRIPT
)
if SPEC is None or SPEC.loader is None:
    raise ImportError(f"cannot load interval certificate at {CERTIFICATE_SCRIPT}")
certificate = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = certificate
SPEC.loader.exec_module(certificate)


def test_interval_schur_inertia_certifies_a1_ground_and_e_doublet_through_level_12():
    results = certificate.certify_spectrum(
        max_level=12,
        dps=2450,
        radius_digits=2390,
    )
    assert len(results) == 12
    for row in results:
        assert all(row["A1"]["checks"].values()), row["A1"]["checks"]
        assert all(row["E"]["checks"].values()), row["E"]["checks"]
        assert Decimal(row["A1"]["upper"]) < Decimal(row["E"]["lower"])
        assert row["A1"]["min_pivot_lower"] > Decimal("1.15")
        assert row["E"]["min_pivot_lower"] > Decimal("1.15")

    level_twelve = results[-1]
    assert (
        Decimal(level_twelve["E"]["lower"])
        - Decimal(level_twelve["A1"]["upper"])
        > Decimal("9.9e-2327")
    )


def test_interval_arithmetic_rejects_a_denominator_interval_containing_zero():
    interval = certificate.DecimalInterval.bounds("-1", "1", 80)
    with __import__("pytest").raises(ZeroDivisionError):
        certificate.DecimalInterval.point(1, 80) / interval
