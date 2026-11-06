#!/usr/bin/env python3
"""Outward-rounded Schur/inertia certificates for finite-level bottom modes.

The exact three-corner Schur matrix is S_m=(a_m-b_m)I+b_m J. At each
three-cell gluing step the midpoint pivot is C_k=c_k I+b_k J, whose
eigenvalues are c_k (twice) and c_k+3b_k (once).

Candidate roots are generated at high precision, then enclosed by decimal
intervals. Every interval operation uses ROUND_FLOOR/ROUND_CEILING. Endpoint
signs, a negative characteristic derivative, b_m<0, the other boundary
channel, and every midpoint pivot are checked independently.

Together with the exact block Schur identity and Sylvester inertia, this
certifies for the requested finite levels that A1 is the simple ground state
and E is the next eigenvalue with multiplicity two. This is not an
infinite-level convergence proof or a Lean-kernel theorem.
"""
from __future__ import annotations

import argparse
import importlib.util
from dataclasses import dataclass
from decimal import Decimal, ROUND_CEILING, ROUND_FLOOR, localcontext
from pathlib import Path

from mpmath import mp

_SCHUR_PATH = Path(__file__).with_name("schur_decimation.py")
_SPEC = importlib.util.spec_from_file_location("schur_decimation_for_certificate", _SCHUR_PATH)
if _SPEC is None or _SPEC.loader is None:
    raise ImportError(f"cannot load Schur recursion at {_SCHUR_PATH}")
schur_decimation = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(schur_decimation)


def _directed(a, b, operation, precision, rounding):
    with localcontext() as context:
        context.prec = precision
        context.rounding = rounding
        if operation == "add":
            return a + b
        if operation == "mul":
            return a * b
        if operation == "div":
            return a / b
    raise ValueError(f"unknown Decimal operation: {operation}")


@dataclass(frozen=True)
class DecimalInterval:
    lo: Decimal
    hi: Decimal
    precision: int

    def __post_init__(self):
        if self.lo > self.hi:
            raise ValueError("empty interval")

    @classmethod
    def point(cls, value, precision):
        exact = value if isinstance(value, Decimal) else Decimal(str(value))
        return cls(exact, exact, precision)

    @classmethod
    def bounds(cls, lower, upper, precision):
        return cls(Decimal(lower), Decimal(upper), precision)

    def __add__(self, other):
        if not isinstance(other, DecimalInterval):
            other = DecimalInterval.point(other, self.precision)
        return DecimalInterval(
            _directed(self.lo, other.lo, "add", self.precision, ROUND_FLOOR),
            _directed(self.hi, other.hi, "add", self.precision, ROUND_CEILING),
            self.precision,
        )

    __radd__ = __add__

    def __neg__(self):
        return DecimalInterval(
            self.hi.copy_negate(), self.lo.copy_negate(), self.precision
        )

    def __sub__(self, other):
        if not isinstance(other, DecimalInterval):
            other = DecimalInterval.point(other, self.precision)
        return self + (-other)

    def __rsub__(self, other):
        return DecimalInterval.point(other, self.precision) - self

    def __mul__(self, other):
        if not isinstance(other, DecimalInterval):
            other = DecimalInterval.point(other, self.precision)
        lowers = [
            _directed(x, y, "mul", self.precision, ROUND_FLOOR)
            for x in (self.lo, self.hi)
            for y in (other.lo, other.hi)
        ]
        uppers = [
            _directed(x, y, "mul", self.precision, ROUND_CEILING)
            for x in (self.lo, self.hi)
            for y in (other.lo, other.hi)
        ]
        return DecimalInterval(min(lowers), max(uppers), self.precision)

    __rmul__ = __mul__

    def __truediv__(self, other):
        if not isinstance(other, DecimalInterval):
            other = DecimalInterval.point(other, self.precision)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError("interval denominator contains zero")
        lowers = [
            _directed(x, y, "div", self.precision, ROUND_FLOOR)
            for x in (self.lo, self.hi)
            for y in (other.lo, other.hi)
        ]
        uppers = [
            _directed(x, y, "div", self.precision, ROUND_CEILING)
            for x in (self.lo, self.hi)
            for y in (other.lo, other.hi)
        ]
        return DecimalInterval(min(lowers), max(uppers), self.precision)

    def square(self):
        if self.lo >= 0:
            lower = _directed(self.lo, self.lo, "mul", self.precision, ROUND_FLOOR)
            upper = _directed(self.hi, self.hi, "mul", self.precision, ROUND_CEILING)
        elif self.hi <= 0:
            lower = _directed(self.hi, self.hi, "mul", self.precision, ROUND_FLOOR)
            upper = _directed(self.lo, self.lo, "mul", self.precision, ROUND_CEILING)
        else:
            lower = Decimal(0)
            left = _directed(self.lo, self.lo, "mul", self.precision, ROUND_CEILING)
            right = _directed(self.hi, self.hi, "mul", self.precision, ROUND_CEILING)
            upper = max(left, right)
        return DecimalInterval(lower, upper, self.precision)

    def positive(self):
        return self.lo > 0

    def negative(self):
        return self.hi < 0


def _schur_interval(lam, level):
    precision = lam.precision
    a = DecimalInterval.point(2, precision) - lam
    da = DecimalInterval.point(-1, precision)
    b = DecimalInterval.point(1, precision)
    db = DecimalInterval.point(0, precision)
    pivot_lowers = []

    for step in range(level):
        c = 2 * a + lam - b
        dc = 2 * da + 1 - db
        c3 = c + 3 * b
        if not c.positive() or not c3.positive():
            raise ArithmeticError(f"midpoint pivot not positive at step {step}")
        pivot_lowers.extend((c.lo, c3.lo))

        den = c * c3
        dden = dc * c3 + c * (dc + 3 * db)
        na = b.square() * (c + b)
        dna = 2 * b * db * (c + b) + b.square() * (dc + db)
        nb = b.square() * (c - b)
        dnb = 2 * b * db * (c - b) + b.square() * (dc - db)

        anew = a - 2 * na / den
        danew = da - 2 * (dna * den - na * dden) / den.square()
        bnew = -nb / den
        dbnew = -(dnb * den - nb * dden) / den.square()
        a, da, b, db = anew, danew, bnew, dbnew

    return a, b, da, db, pivot_lowers


def _root_bracket(root, dps, radius_digits):
    if dps < radius_digits + 40:
        raise ValueError("dps must exceed radius_digits by at least 40")
    with mp.workdps(dps):
        radius = mp.power(10, -radius_digits)
        lower = mp.nstr(root - radius, dps - 10)
        upper = mp.nstr(root + radius, dps - 10)
    if Decimal(lower) >= Decimal(upper):
        raise ArithmeticError("unordered root bracket")
    return lower, upper


def certify_boundary_root(root, level, sector, dps=2450, radius_digits=2390):
    sector = sector.upper()
    if sector not in {"A1", "E"}:
        raise ValueError("sector must be A1 or E")
    lower, upper = _root_bracket(root, dps, radius_digits)
    whole = DecimalInterval.bounds(lower, upper, dps)
    a, b, da, db, pivots = _schur_interval(whole, level)

    if sector == "A1":
        derivative, other = da + 2 * db, a - b
    else:
        derivative, other = da - db, a + 2 * b

    a_lo, b_lo, _, _, _ = _schur_interval(
        DecimalInterval.point(Decimal(lower), dps), level
    )
    a_hi, b_hi, _, _, _ = _schur_interval(
        DecimalInterval.point(Decimal(upper), dps), level
    )
    left = a_lo + 2 * b_lo if sector == "A1" else a_lo - b_lo
    right = a_hi + 2 * b_hi if sector == "A1" else a_hi - b_hi

    checks = {
        "left_endpoint_positive": left.positive(),
        "right_endpoint_negative": right.negative(),
        "derivative_negative": derivative.negative(),
        "b_negative": b.negative(),
        "other_channel_sign": other.positive() if sector == "A1" else other.negative(),
        "all_midpoint_pivots_positive": all(value > 0 for value in pivots),
    }
    if not all(checks.values()):
        failed = [name for name, passed in checks.items() if not passed]
        raise ArithmeticError(f"{sector} level {level} failed: {failed}")

    return {
        "level": level,
        "sector": sector,
        "lower": lower,
        "upper": upper,
        "checks": checks,
        "min_pivot_lower": min(pivots),
        "derivative_upper": derivative.hi,
        "b_upper": b.hi,
    }


def certify_spectrum(max_level=12, dps=2450, radius_digits=2390):
    if max_level < 1:
        raise ValueError("max_level must be at least one")
    a1_roots = schur_decimation.a1_boundary_root_sequence(max_level, dps=dps)
    e_roots = schur_decimation.e_boundary_root_sequence(max_level, dps=dps)

    results = []
    for level in range(1, max_level + 1):
        a1_cert = certify_boundary_root(
            a1_roots[level], level, "A1", dps, radius_digits
        )
        e_cert = certify_boundary_root(
            e_roots[level], level, "E", dps, radius_digits
        )
        if Decimal(a1_cert["upper"]) >= Decimal(e_cert["lower"]):
            raise ArithmeticError(f"A1/E brackets overlap at level {level}")
        results.append(
            {
                "level": level,
                "A1": a1_cert,
                "E": e_cert,
                "A1_approx": mp.nstr(a1_roots[level], 80),
                "E_approx": mp.nstr(e_roots[level], 80),
            }
        )
    return results


def main():
    parser = argparse.ArgumentParser(
        description="Finite-level interval/inertia certificate for A1 ground and E doublet."
    )
    parser.add_argument("--max-level", type=int, default=12)
    parser.add_argument("--dps", type=int, default=2450)
    parser.add_argument("--radius-digits", type=int, default=2390)
    args = parser.parse_args()

    results = certify_spectrum(args.max_level, args.dps, args.radius_digits)
    min_pivot = min(
        min(row["A1"]["min_pivot_lower"], row["E"]["min_pivot_lower"])
        for row in results
    )
    for row in results:
        print(
            f"level {row['level']}: A1 simple ground state certified; "
            "E doublet certified as next eigenvalue"
        )
        print(f"  A1 ~ {row['A1_approx']}")
        print(f"  E  ~ {row['E_approx']}")
    print(
        f"SUMMARY: levels 1..{args.max_level} certified; "
        "minimum midpoint-pivot lower bound="
        f"{min_pivot}"
    )
    print(
        "Scope: finite-level interval/inertia certificates only; "
        "no infinite-level convergence theorem is claimed."
    )


if __name__ == "__main__":
    main()
