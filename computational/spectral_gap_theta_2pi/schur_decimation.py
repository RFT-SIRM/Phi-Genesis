#!/usr/bin/env python3
"""Exact scalar Schur-complement recursion for the S3-symmetric A1 sector.

For the signless gasket Laplacian Q = D + A, let S_m(lambda) be the
Dirichlet-to-Neumann (Schur-complement) matrix obtained from Q_m-lambda I
by eliminating every non-corner vertex. S3 symmetry forces

    S_m(lambda) = (a_m(lambda)-b_m(lambda)) I_3 + b_m(lambda) J_3.

The functions a_m and b_m are rational in lambda and obey the exact
three-cell recursion implemented below. The A1 boundary-characteristic
root is a_m + 2*b_m = 0, away from poles of the eliminated interior block.

This is an exact finite-level algebraic recursion. Root finding is numerical;
residuals are diagnostics, not interval certificates, and the routine does
not by itself prove that every returned root is the lowest A1 eigenvalue.
"""
from __future__ import annotations

import argparse

from mpmath import mp


def schur_parameters(lam, level: int):
    """Return (a_m,b_m) for the level-m 3x3 boundary Schur complement."""
    if level < 0:
        raise ValueError("level must be nonnegative")
    a = mp.mpf(2) - lam
    b = mp.mpf(1)
    for _ in range(level):
        c = 2 * a + lam - b
        denominator = c * (c + 3 * b)
        if denominator == 0:
            raise ZeroDivisionError("Schur recursion reached a Dirichlet pole")
        a_next = a - 2 * b**2 * (c + b) / denominator
        b_next = -b**2 * (c - b) / denominator
        a, b = a_next, b_next
    return a, b


def a1_characteristic(lam, level: int):
    """Return the symmetric-boundary eigenvalue a_m(lambda)+2 b_m(lambda)."""
    a, b = schur_parameters(lam, level)
    return a + 2 * b


def a1_characteristic_with_derivative(lam, level: int):
    """Return the characteristic and its exact forward-mode derivative."""
    if level < 0:
        raise ValueError("level must be nonnegative")

    a, da = mp.mpf(2) - lam, mp.mpf(-1)
    b, db = mp.mpf(1), mp.mpf(0)
    for _ in range(level):
        c = 2 * a + lam - b
        dc = 2 * da + 1 - db
        denominator = c * (c + 3 * b)
        d_denominator = dc * (c + 3 * b) + c * (dc + 3 * db)
        if denominator == 0:
            raise ZeroDivisionError("Schur recursion reached a Dirichlet pole")

        numerator_a = b**2 * (c + b)
        d_numerator_a = 2 * b * db * (c + b) + b**2 * (dc + db)
        numerator_b = b**2 * (c - b)
        d_numerator_b = 2 * b * db * (c - b) + b**2 * (dc - db)

        a_next = a - 2 * numerator_a / denominator
        da_next = da - 2 * (
            d_numerator_a * denominator
            - numerator_a * d_denominator
        ) / denominator**2
        b_next = -numerator_b / denominator
        db_next = -(
            d_numerator_b * denominator
            - numerator_b * d_denominator
        ) / denominator**2
        a, da = a_next, da_next
        b, db = b_next, db_next

    return a + 2 * b, da + 2 * db


def _newton_refine(level: int, initial, dps: int, max_iterations: int = 40):
    x = mp.mpf(initial)
    target_step = mp.power(10, -dps + 12)
    for _ in range(max_iterations):
        value, derivative = a1_characteristic_with_derivative(x, level)
        if derivative == 0:
            raise ArithmeticError(f"zero characteristic derivative at level {level}")
        step = value / derivative
        next_x = x - step
        if next_x == x:
            break
        x = next_x
        if abs(step) <= target_step:
            break
    else:
        raise RuntimeError(f"Newton refinement did not converge at level {level}")

    if x <= initial:
        raise ArithmeticError(
            f"working precision cannot resolve the level-{level} increment"
        )
    residual = abs(a1_characteristic(x, level))
    if residual > mp.power(10, -dps + 8):
        raise ArithmeticError(
            f"level-{level} characteristic residual too large: {mp.nstr(residual, 8)}"
        )
    return x


def a1_boundary_root_sequence(max_level: int, dps: int = 100):
    """Compute the continued low A1 boundary-characteristic root sequence.

    Levels 1 and 2 are initialized from fixed secant seeds. Each later root
    is obtained by Newton continuation from the preceding level. The routine
    raises rather than silently repeating a previous value when dps cannot
    resolve a new, much smaller level increment. It does not independently
    certify that the continued root is the lowest A1 eigenvalue at every level.
    """
    if max_level < 1:
        raise ValueError("max_level must be at least one")
    if dps < 50:
        raise ValueError("dps must be at least 50")

    with mp.workdps(dps):
        roots = {
            1: mp.findroot(
                lambda x: a1_characteristic(x, 1),
                (mp.mpf("1.1"), mp.mpf("1.2")),
                tol=mp.power(10, -dps + 10),
                maxsteps=100,
            )
        }
        if abs(a1_characteristic(roots[1], 1)) > mp.power(10, -dps + 8):
            raise ArithmeticError("level-one boundary root failed its residual check")

        if max_level >= 2:
            roots[2] = mp.findroot(
                lambda x: a1_characteristic(x, 2),
                (mp.mpf("1.29"), mp.mpf("1.30")),
                tol=mp.power(10, -dps + 10),
                maxsteps=100,
            )
            if roots[2] <= roots[1]:
                raise ArithmeticError("level-two root did not advance")
            if abs(a1_characteristic(roots[2], 2)) > mp.power(10, -dps + 8):
                raise ArithmeticError("level-two boundary root failed its residual check")

        for level in range(3, max_level + 1):
            roots[level] = _newton_refine(
                level, roots[level - 1], dps=dps
            )
            if roots[level] <= roots[level - 1]:
                raise ArithmeticError(
                    f"level-{level} root did not advance beyond level {level - 1}"
                )
        return roots


def main():
    parser = argparse.ArgumentParser(
        description="Compute A1 boundary-characteristic roots from the exact Schur recursion."
    )
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--dps", type=int, default=360)
    args = parser.parse_args()

    roots = a1_boundary_root_sequence(args.max_level, args.dps)
    with mp.workdps(args.dps):
        increments = {
            level: roots[level] - roots[level - 1]
            for level in range(2, args.max_level + 1)
        }
        for level in range(1, args.max_level + 1):
            print(
                f"A1 boundary root {level}: "
                f"{mp.nstr(roots[level], min(100, args.dps - 5))}"
            )
            if level >= 2:
                print(
                    f"  delta_{level}="
                    f"{mp.nstr(increments[level], 50)}"
                )
            if level >= 3:
                ratio = increments[level] / increments[level - 1] ** 2
                print(
                    f"  ratio_{level}="
                    f"{mp.nstr(ratio, 50)}"
                )
        print(
            "NOTE: exact Schur recursion; numerical roots/residuals are not "
            "interval certificates or a proof of the infinite-level limit."
        )


if __name__ == "__main__":
    main()
