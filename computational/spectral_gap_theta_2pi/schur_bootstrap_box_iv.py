#!/usr/bin/env python3
"""Finite interval bootstrap experiment for the A1 Schur recursion.

An asymmetric interval around the level-6 A1 root is propagated through the
exact three-corner Schur recursion. At each finite level this checks the A1
endpoint signs, derivative and curvature windows, midpoint pivots, and the
proposed bootstrap box. It does not prove that the box is invariant for all
levels.
"""
from __future__ import annotations

import argparse
from mpmath import iv, mp


def _numeric_a1(lam, level):
    """A1 characteristic and first derivative, using mpmath scalars."""
    a, da = mp.mpf(2) - lam, mp.mpf(-1)
    b, db = mp.mpf(1), mp.mpf(0)
    for _ in range(level):
        c = 2 * a + lam - b
        dc = 2 * da + 1 - db
        den = c * (c + 3 * b)
        dden = dc * (c + 3 * b) + c * (dc + 3 * db)
        na = b**2 * (c + b)
        dna = 2 * b * db * (c + b) + b**2 * (dc + db)
        nb = b**2 * (c - b)
        dnb = 2 * b * db * (c - b) + b**2 * (dc - db)
        a, da = a - 2 * na / den, da - 2 * (dna * den - na * dden) / den**2
        b, db = -nb / den, -(dnb * den - nb * dden) / den**2
    return a + 2 * b, da + 2 * db


def _level_six_root(dps):
    with mp.workdps(dps):
        root = mp.findroot(lambda x: _numeric_a1(x, 1)[0], ("1.1", "1.2"), tol=mp.power(10, -dps + 12))
        root = mp.findroot(lambda x: _numeric_a1(x, 2)[0], ("1.29", "1.30"), tol=mp.power(10, -dps + 12))
        for level in range(3, 7):
            x = +root
            for _ in range(50):
                value, derivative = _numeric_a1(x, level)
                if derivative == 0:
                    raise ArithmeticError(f"zero A1 derivative at level {level}")
                step = value / derivative
                x -= step
                if abs(step) < mp.power(10, -dps + 12):
                    break
            else:
                raise ArithmeticError(f"Newton iteration failed at level {level}")
            root = x
        return +root


def _interval_state(x, level):
    """Propagate (a,b) and first two lambda derivatives outwardly."""
    a, da, dda = iv.mpf(2) - x, iv.mpf(-1), iv.mpf(0)
    b, db, ddb = iv.mpf(1), iv.mpf(0), iv.mpf(0)
    pivots = []
    for step in range(level):
        c = 2 * a + x - b
        dc = 2 * da + 1 - db
        ddc = 2 * dda - ddb
        c3 = c + 3 * b
        dc3 = dc + 3 * db
        ddc3 = ddc + 3 * ddb
        if not (c.a > 0 and c3.a > 0):
            raise ArithmeticError(f"nonpositive midpoint pivot at step {step}")
        pivots.extend((c, c3))
        den = c * c3
        dden = dc * c3 + c * dc3
        d2den = ddc * c3 + 2 * dc * dc3 + c * ddc3
        w, dw, d2w = c + b, dc + db, ddc + ddb
        na = b * b * w
        dna = 2 * b * db * w + b * b * dw
        d2na = (2 * db * db + 2 * b * ddb) * w + 4 * b * db * dw + b * b * d2w
        z, dz, d2z = c - b, dc - db, ddc - ddb
        nb = b * b * z
        dnb = 2 * b * db * z + b * b * dz
        d2nb = (2 * db * db + 2 * b * ddb) * z + 4 * b * db * dz + b * b * d2z
        den2, den3 = den * den, den * den * den
        daq = (dna * den - na * dden) / den2
        d2aq = d2na / den - na * d2den / den2 - 2 * dna * dden / den2 + 2 * na * dden * dden / den3
        dbq = (dnb * den - nb * dden) / den2
        d2bq = d2nb / den - nb * d2den / den2 - 2 * dnb * dden / den2 + 2 * nb * dden * dden / den3
        a, da, dda = a - 2 * na / den, da - 2 * daq, dda - 2 * d2aq
        b, db, ddb = -nb / den, -dbq, -d2bq
    return a, b, da, db, dda, ddb, pivots


def _inside(x, lo, hi):
    return mp.mpf(lo) <= x.a and x.b <= mp.mpf(hi)


def _lower(x):
    return mp.make_mpf(x._mpi_[0])


def _upper(x):
    return mp.make_mpf(x._mpi_[1])


def _endpoint_f(lam, level):
    a, b, *_ = _interval_state(iv.mpf(lam), level)
    return a + 2 * b


def certify_bootstrap(max_level=101, dps=180, radius_digits=140):
    if max_level < 7 or dps < radius_digits + 30:
        raise ValueError("require max_level>=7 and dps>=radius_digits+30")
    with mp.workdps(dps):
        root6 = _level_six_root(dps)
        lower = mp.nstr(root6 - mp.power(10, -radius_digits), dps - 20)
        upper = mp.nstr(root6 + mp.mpf("1.1e-36"), dps - 20)
        shift_bound = 2 * mp.mpf("6e-37") / (mp.mpf("1.292") * (1 - mp.mpf("0.8") * mp.mpf("6e-37")))
    iv.dps = dps
    lam = iv.mpf([lower, upper])
    min_pivot, max_contraction = None, mp.mpf(0)
    snapshots = []
    endpoint_values = {}
    level6_a_bounds = None
    for level in range(6, max_level + 1):
        a, b, da, db, dda, ddb, pivots = _interval_state(lam, level)
        fprime, fsecond = da + 2 * db, dda + 2 * ddb
        checks = {
            "a": _inside(a, "-1e-35", "1e-35"),
            "b": _inside(b, "-6e-37", "0"),
            "a_prime": _inside(da, "-1.294", "-1.292"),
            "b_prime": _inside(db, "-1.1e-35", "1.1e-35"),
            "a_second": _inside(dda, "-0.286", "-0.281"),
            "b_second": _inside(ddb, "-2.1e-34", "2.1e-34"),
            "A1_prime": _inside(fprime, "-1.294", "-1.292"),
            "A1_second": _inside(fsecond, "-0.286", "-0.281"),
        }
        if not all(checks.values()):
            raise ArithmeticError(f"bootstrap box failed at level {level}: {[k for k,v in checks.items() if not v]}")
        if not all(p.a > 0 for p in pivots):
            raise ArithmeticError(f"nonpositive pivot at level {level}")
        if level == 6:
            if not _inside(a, "-3e-36", "3e-36"):
                raise ArithmeticError("level-6 diagonal coefficient leaves the sharpened initial box")
            level6_a_bounds = (_lower(a.a), _upper(a.b))
        c = 2 * a + lam - b
        c3 = c + 3 * b
        for p in (c, c3):
            pv = _lower(p.a)
            min_pivot = pv if min_pivot is None else min(min_pivot, pv)
        ratio = (c - b) / (c * c3)
        if not (ratio.a > 0 and ratio.b < iv.mpf("0.8")):
            raise ArithmeticError(f"off-diagonal contraction outside (0,0.8) at level {level}")
        max_contraction = max(max_contraction, mp.make_mpf(ratio.b._mpi_[0]))
        left_f, right_f = _endpoint_f(lower, level), _endpoint_f(upper, level)
        if not (left_f.a > 0 and right_f.b < 0):
            raise ArithmeticError(f"A1 root not bracketed at level {level}")
        endpoint_values[level] = (_lower(left_f.a), _upper(right_f.b))
        if level in {6,7,8,10,14,20,50,max_level}:
            snapshots.append((level,_lower(b.a),_upper(b.b),_lower(fprime.a),_upper(fprime.b),_lower(fsecond.a),_upper(fsecond.b)))
    return {
        "root6":mp.nstr(root6,80),"lower":lower,"upper":upper,
        "level6_a_lower":mp.nstr(level6_a_bounds[0],60),
        "level6_a_upper":mp.nstr(level6_a_bounds[1],60),
        "level6_left_f":mp.nstr(endpoint_values[6][0],35),"level6_right_f":mp.nstr(endpoint_values[6][1],35),
        "final_left_f":mp.nstr(endpoint_values[max_level][0],35),"final_right_f":mp.nstr(endpoint_values[max_level][1],35),
        "min_pivot_lower":mp.nstr(min_pivot,60),"max_contraction_upper":mp.nstr(max_contraction,60),
        "conditional_root_shift_bound":mp.nstr(shift_bound,40),"snapshots":snapshots,"max_level":max_level,
    }


def main():
    parser=argparse.ArgumentParser(description="Finite A1 Schur bootstrap-window interval experiment.")
    parser.add_argument("--max-level",type=int,default=101)
    parser.add_argument("--dps",type=int,default=180)
    parser.add_argument("--radius-digits",type=int,default=140)
    args=parser.parse_args()
    r=certify_bootstrap(args.max_level,args.dps,args.radius_digits)
    print(f"level-6 A1 root candidate: {r['root6']}")
    print(f"fixed asymmetric parameter window: [{r['lower']}, {r['upper']}]")
    print(f"level-6 endpoint signs: {r['level6_left_f']} > 0; {r['level6_right_f']} < 0")
    print(f"level-6 diagonal interval: [{r['level6_a_lower']}, {r['level6_a_upper']}]")
    print(f"root endpoint signs checked at every level through {r['max_level']}")
    print(f"minimum midpoint-pivot lower endpoint: {r['min_pivot_lower']}")
    print(f"maximum |b_next|/|b|^2 upper endpoint: {r['max_contraction_upper']}")
    print(f"conditional all-future root-shift budget: {r['conditional_root_shift_bound']}")
    print("Scope: finite interval propagation only; no all-level theorem is claimed.")
    for level,blo,bhi,fplo,fphi,fpplo,fpphi in r["snapshots"]:
        print(f"level {level}: b in [{blo}, {bhi}], f' in [{fplo}, {fphi}], f'' in [{fpplo}, {fpphi}]")


if __name__ == "__main__":
    main()
