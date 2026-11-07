#!/usr/bin/env python3
"""Outward-rounded certificate for the A1 derivative step along root transitions.

For D_m = f'_m(lambda_m), the exact Schur identity gives
  G_m = f'_(m+1)(lambda_m) - f'_m(lambda_m)
      = -2 b'_m R_m - 2 b_m R'_m.
On the interval containing [lambda_m, lambda_(m+1)], interval propagation
bounds f''_(m+1). The mean-value theorem controls the remaining root shift.

This certifies finite transitions only; it does not claim the bounds hold
for every level.
"""
from __future__ import annotations

import argparse
import importlib.util
import sys
from pathlib import Path

from mpmath import iv, mp

sys.set_int_max_str_digits(0)

_SCHUR_PATH = Path(__file__).with_name("schur_decimation.py")
_SPEC = importlib.util.spec_from_file_location(
    "schur_decimation_for_derivative_certificate", _SCHUR_PATH
)
if _SPEC is None or _SPEC.loader is None:
    raise ImportError(f"cannot load Schur recursion at {_SCHUR_PATH}")
schur_decimation = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(schur_decimation)


def _schur_interval_second_order(x, level):
    """Propagate (a,b) and their first two lambda derivatives outwardly."""
    a, da, dda = iv.mpf(2) - x, iv.mpf(-1), iv.mpf(0)
    b, db, ddb = iv.mpf(1), iv.mpf(0), iv.mpf(0)
    pivot_intervals = []

    for step in range(level):
        c = 2 * a + x - b
        dc = 2 * da + 1 - db
        ddc = 2 * dda - ddb
        c3 = c + 3 * b
        dc3 = dc + 3 * db
        ddc3 = ddc + 3 * ddb
        if not (c.a > 0 and c3.a > 0):
            raise ArithmeticError(f"nonpositive midpoint pivot at step {step}")
        pivot_intervals.extend((c, c3))

        denominator = c * c3
        d_denominator = dc * c3 + c * dc3
        d2_denominator = ddc * c3 + 2 * dc * dc3 + c * ddc3

        w = c + b
        dw = dc + db
        d2w = ddc + ddb
        numerator_a = b * b * w
        d_numerator_a = 2 * b * db * w + b * b * dw
        d2_numerator_a = (
            (2 * db * db + 2 * b * ddb) * w
            + 4 * b * db * dw
            + b * b * d2w
        )

        z = c - b
        dz = dc - db
        d2z = ddc - ddb
        numerator_b = b * b * z
        d_numerator_b = 2 * b * db * z + b * b * dz
        d2_numerator_b = (
            (2 * db * db + 2 * b * ddb) * z
            + 4 * b * db * dz
            + b * b * d2z
        )

        denominator_sq = denominator * denominator
        denominator_cube = denominator_sq * denominator
        da_quotient = (
            d_numerator_a * denominator - numerator_a * d_denominator
        ) / denominator_sq
        d2a_quotient = (
            d2_numerator_a / denominator
            - numerator_a * d2_denominator / denominator_sq
            - 2 * d_numerator_a * d_denominator / denominator_sq
            + 2 * numerator_a * d_denominator * d_denominator / denominator_cube
        )
        db_quotient = (
            d_numerator_b * denominator - numerator_b * d_denominator
        ) / denominator_sq
        d2b_quotient = (
            d2_numerator_b / denominator
            - numerator_b * d2_denominator / denominator_sq
            - 2 * d_numerator_b * d_denominator / denominator_sq
            + 2 * numerator_b * d_denominator * d_denominator / denominator_cube
        )

        a_new = a - 2 * numerator_a / denominator
        da_new = da - 2 * da_quotient
        dda_new = dda - 2 * d2a_quotient
        b_new = -numerator_b / denominator
        db_new = -db_quotient
        ddb_new = -d2b_quotient
        a, da, dda, b, db, ddb = a_new, da_new, dda_new, b_new, db_new, ddb_new

    return a, b, da, db, dda, ddb, pivot_intervals


def _root_bracket(root, dps, radius_digits):
    if dps < radius_digits + 40:
        raise ValueError("dps must exceed radius_digits by at least 40")
    with mp.workdps(dps):
        radius = mp.power(10, -radius_digits)
        lower = mp.nstr(root - radius, dps - 20)
        upper = mp.nstr(root + radius, dps - 20)
    return lower, upper


def _endpoint_characteristic(endpoint, level):
    a, b, *_ = _schur_interval_second_order(iv.mpf(endpoint), level)
    return a + 2 * b


def certify_derivative_transitions(
    max_level=14,
    dps=10000,
    radius_digits=9400,
    start_level=5,
):
    """Certify A1 root boxes and derivative shifts for transitions start..max-1."""
    if start_level < 1 or max_level <= start_level:
        raise ValueError("require 1 <= start_level < max_level")
    if dps < radius_digits + 40:
        raise ValueError("dps must exceed radius_digits by at least 40")

    with mp.workdps(dps):
        roots = schur_decimation.a1_boundary_root_sequence(max_level, dps=dps)
        iv.dps = radius_digits + 100
        root_boxes = {}
        root_data = {}

        for level in range(start_level, max_level + 1):
            lower, upper = _root_bracket(roots[level], dps, radius_digits)
            whole = iv.mpf([lower, upper])
            a, b, da, db, _dda, _ddb, pivots = _schur_interval_second_order(whole, level)
            derivative = da + 2 * db
            other_channel = a - b
            left = _endpoint_characteristic(lower, level)
            right = _endpoint_characteristic(upper, level)
            checks = {
                "left_endpoint_positive": left.a > 0,
                "right_endpoint_negative": right.b < 0,
                "derivative_negative": derivative.b < 0,
                "off_diagonal_negative": b.b < 0,
                "E_channel_positive": other_channel.a > 0,
                "all_midpoint_pivots_positive": all(p.a > 0 for p in pivots),
            }
            if not all(checks.values()):
                failed = [name for name, passed in checks.items() if not passed]
                raise ArithmeticError(f"A1 level {level} failed: {failed}")
            root_boxes[level] = (lower, upper)
            root_data[level] = (whole, a, b, da, db)

        rows = []
        for level in range(start_level, max_level):
            lower, _ = root_boxes[level]
            _, next_upper = root_boxes[level + 1]
            if mp.mpf(next_upper) <= mp.mpf(lower):
                raise ArithmeticError(f"A1 root boxes are not ordered at {level}->{level + 1}")

            # This interval contains the exact segment [lambda_m, lambda_(m+1)].
            segment = iv.mpf([lower, next_upper])
            _a, _b, _da, _db, dda, ddb, segment_pivots = (
                _schur_interval_second_order(segment, level + 1)
            )
            curvature = dda + 2 * ddb
            if not (
                curvature.a > iv.mpf("-0.29")
                and curvature.b < iv.mpf("-0.07")
            ):
                raise ArithmeticError(
                    f"A1 curvature bound failed on transition {level}->{level + 1}: {curvature}"
                )
            if not all(p.a > 0 for p in segment_pivots):
                raise ArithmeticError(f"midpoint pivot failed on segment {level}->{level + 1}")

            # G_m = f'_(m+1)(lambda_m) - f'_m(lambda_m), from the exact
            # differentiated Schur update f_(m+1)=f_m-2*b_m*R_m.
            _whole, a_old, b_old, da_old, db_old = root_data[level]
            lam = iv.mpf([lower, root_boxes[level][1]])
            c = 2 * a_old + lam - b_old
            dc = 2 * da_old + 1 - db_old
            denominator = c + 3 * b_old
            ratio = (c + 5 * b_old) / denominator
            ratio_derivative = (
                2 * (c * db_old - b_old * dc) / (denominator * denominator)
            )
            g = -2 * db_old * ratio - 2 * b_old * ratio_derivative

            abs_g = abs(g)
            abs_b = -b_old
            abs_b_next = -root_data[level + 1][2]
            abs_g_upper = mp.make_mpf(abs_g.b._mpi_[0])
            abs_b_lower = mp.make_mpf(abs_b.a._mpi_[0])
            abs_b_next_upper = mp.make_mpf(abs_b_next.b._mpi_[0])
            if abs_b_lower <= 0:
                raise ArithmeticError(f"off-diagonal lower bound failed at level {level}")

            increment_upper = (
                mp.mpf(root_boxes[level + 1][1]) - mp.mpf(root_boxes[level][0])
            )
            g_ratio_upper = abs_g_upper / (mp.mpf(2) ** level * abs_b_lower)
            total_variation_upper = abs_g_upper + mp.mpf("0.29") * increment_upper
            derivative_ratio_upper = (
                total_variation_upper / (mp.mpf(2) ** level * abs_b_lower)
            )
            contraction_ratio_upper = abs_b_next_upper / (abs_b_lower * abs_b_lower)

            if not (g_ratio_upper < mp.mpf("0.7")):
                raise ArithmeticError(f"Schur derivative correction too large at level {level}")
            if not (derivative_ratio_upper < 1):
                raise ArithmeticError(f"root-sampled derivative variation too large at level {level}")
            if not (contraction_ratio_upper < mp.mpf("0.8")):
                raise ArithmeticError(f"root-sampled b contraction failed at level {level}")

            curvature_lower = mp.make_mpf(curvature.a._mpi_[0])
            curvature_upper = mp.make_mpf(curvature.b._mpi_[0])
            rows.append({
                "level": level,
                "curvature_lower": curvature_lower,
                "curvature_upper": curvature_upper,
                "g_ratio_upper": g_ratio_upper,
                "derivative_variation_ratio_upper": derivative_ratio_upper,
                "b_contraction_ratio_upper": contraction_ratio_upper,
                "increment_upper": increment_upper,
                "b_abs_lower": abs_b_lower,
                "pivot_lower": min(mp.make_mpf(p.a._mpi_[0]) for p in segment_pivots),
            })
        return rows


def main():
    parser = argparse.ArgumentParser(
        description="Interval certificate for the A1 Schur derivative along successive root segments."
    )
    parser.add_argument("--max-level", type=int, default=14)
    parser.add_argument("--start-level", type=int, default=5)
    parser.add_argument("--dps", type=int, default=10000)
    parser.add_argument("--radius-digits", type=int, default=9400)
    args = parser.parse_args()

    rows = certify_derivative_transitions(
        args.max_level, args.dps, args.radius_digits, args.start_level
    )
    for row in rows:
        print(
            f"transition {row['level']}->{row['level'] + 1}: "
            f"f'' in ({mp.nstr(row['curvature_lower'], 24)}, "
            f"{mp.nstr(row['curvature_upper'], 24)}), "
            f"G/(2^m|b_m|)<{mp.nstr(row['g_ratio_upper'], 12)}, "
            f"|D_(m+1)-D_m|/(2^m|b_m|)<"
            f"{mp.nstr(row['derivative_variation_ratio_upper'], 12)}, "
            f"|b_(m+1)|/|b_m|^2<{mp.nstr(row['b_contraction_ratio_upper'], 12)}"
        )
    print(
        f"SUCCESS: transitions {args.start_level}..{args.max_level - 1} "
        "have certified root order, positive pivots, curvature, and derivative bounds."
    )
    print(
        "Scope: finite-level interval certificates only; the estimates still "
        "need a uniform proof for all levels."
    )


if __name__ == "__main__":
    main()
