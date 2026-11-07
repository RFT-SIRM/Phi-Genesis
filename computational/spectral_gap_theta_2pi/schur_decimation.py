#!/usr/bin/env python3
"""Exact scalar Schur-complement recursion for S3-symmetric gasket boundary modes.

For the signless gasket Laplacian Q = D + A, let S_m(lambda) be the
Dirichlet-to-Neumann Schur complement obtained from Q_m-lambda I by
eliminating every non-corner vertex. S3 symmetry forces

    S_m(lambda) = (a_m(lambda)-b_m(lambda)) I_3 + b_m(lambda) J_3.

The exact three-cell rational recursion below computes a_m and b_m. The
A1 boundary channel is a_m+2*b_m; the standard E boundary channel is
a_m-b_m. Numerical root continuation is not an interval certificate and
does not alone prove that a continued root is the lowest eigenvalue.
"""
from __future__ import annotations
import argparse
from mpmath import mp


def schur_parameters(lam, level: int):
    """Return (a_m,b_m) for the level-m 3x3 boundary Schur complement."""
    if level < 0:
        raise ValueError("level must be nonnegative")
    a, b = mp.mpf(2) - lam, mp.mpf(1)
    for _ in range(level):
        c = 2 * a + lam - b
        denominator = c * (c + 3 * b)
        if denominator == 0:
            raise ZeroDivisionError("Schur recursion reached a Dirichlet pole")
        a_next = a - 2 * b**2 * (c + b) / denominator
        b_next = -b**2 * (c - b) / denominator
        a, b = a_next, b_next
    return a, b


def _schur_parameters_with_derivative(lam, level: int):
    """Return a, b and their exact forward-mode derivatives in lambda."""
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
            d_numerator_a * denominator - numerator_a * d_denominator
        ) / denominator**2
        b_next = -numerator_b / denominator
        db_next = -(
            d_numerator_b * denominator - numerator_b * d_denominator
        ) / denominator**2
        a, da, b, db = a_next, da_next, b_next, db_next
    return a, b, da, db


def a1_characteristic(lam, level: int):
    """Return the symmetric-boundary eigenvalue a_m(lambda)+2 b_m(lambda)."""
    a, b = schur_parameters(lam, level)
    return a + 2 * b


def e_characteristic(lam, level: int):
    """Return the standard-boundary eigenvalue a_m(lambda)-b_m(lambda)."""
    a, b = schur_parameters(lam, level)
    return a - b


def a1_characteristic_with_derivative(lam, level: int):
    a, b, da, db = _schur_parameters_with_derivative(lam, level)
    return a + 2 * b, da + 2 * db


def e_characteristic_with_derivative(lam, level: int):
    a, b, da, db = _schur_parameters_with_derivative(lam, level)
    return a - b, da - db


def _initial_root(level: int, guesses, characteristic, dps: int):
    seed_pair = tuple(mp.mpf(value) for value in guesses)
    root = mp.findroot(
        lambda x: characteristic(x, level),
        seed_pair,
        tol=mp.power(10, -dps + 10),
        maxsteps=100,
    )
    residual = abs(characteristic(root, level))
    if residual > mp.power(10, -dps + 8):
        raise ArithmeticError(
            f"level-{level} initial boundary root residual too large: {mp.nstr(residual, 8)}"
        )
    return root


def _newton_refine(
    level: int,
    initial,
    dps: int,
    characteristic_with_derivative,
    direction: int,
    max_iterations: int = 40,
):
    """Refine one root; direction is +1 for increasing, -1 for decreasing roots."""
    x = mp.mpf(initial)
    target_step = mp.power(10, -dps + 12)
    for _ in range(max_iterations):
        value, derivative = characteristic_with_derivative(x, level)
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
    if direction * (x - initial) <= 0:
        raise ArithmeticError(
            f"working precision cannot resolve the level-{level} root shift"
        )
    residual = abs(characteristic_with_derivative(x, level)[0])
    if residual > mp.power(10, -dps + 8):
        raise ArithmeticError(
            f"level-{level} characteristic residual too large: {mp.nstr(residual, 8)}"
        )
    return x


def a1_boundary_root_sequence(max_level: int, dps: int = 100):
    """Continue the low A1 boundary-characteristic root from levels 1 and 2.

    Later roots are obtained by Newton continuation from the preceding level.
    Insufficient dps raises instead of silently repeating the previous root.
    This does not independently prove the selected root is the lowest A1 mode.
    """
    if max_level < 1:
        raise ValueError("max_level must be at least one")
    if dps < 50:
        raise ValueError("dps must be at least 50")
    with mp.workdps(dps):
        roots = {1: _initial_root(1, ("1.1", "1.2"), a1_characteristic, dps)}
        if max_level >= 2:
            roots[2] = _initial_root(2, ("1.29", "1.30"), a1_characteristic, dps)
            if roots[2] <= roots[1]:
                raise ArithmeticError("level-two A1 root did not advance")
        for level in range(3, max_level + 1):
            roots[level] = _newton_refine(
                level, roots[level - 1], dps,
                a1_characteristic_with_derivative, direction=1,
            )
        return roots


def e_boundary_root_sequence(max_level: int, dps: int = 100):
    """Continue the low E boundary-characteristic root from levels 1 and 2.

    The E boundary channel is the two-dimensional subspace orthogonal to the
    constant corner vector. Later roots decrease toward the same limit as A1.
    This does not independently prove the continued root is the lowest E mode.
    """
    if max_level < 1:
        raise ValueError("max_level must be at least one")
    if dps < 50:
        raise ValueError("dps must be at least 50")
    with mp.workdps(dps):
        roots = {1: _initial_root(1, ("1.3", "1.4"), e_characteristic, dps)}
        if max_level >= 2:
            roots[2] = _initial_root(2, ("1.31", "1.32"), e_characteristic, dps)
            if roots[2] >= roots[1]:
                raise ArithmeticError("level-two E root did not decrease")
        for level in range(3, max_level + 1):
            roots[level] = _newton_refine(
                level, roots[level - 1], dps,
                e_characteristic_with_derivative, direction=-1,
            )
        return roots


def main():
    parser = argparse.ArgumentParser(
        description="Compute A1 or E boundary-characteristic roots from the exact Schur recursion."
    )
    parser.add_argument("--sector", choices=("A1", "E"), default="A1")
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--dps", type=int, default=360)
    args = parser.parse_args()
    solver = a1_boundary_root_sequence if args.sector == "A1" else e_boundary_root_sequence
    roots = solver(args.max_level, args.dps)
    with mp.workdps(args.dps):
        changes = {
            level: roots[level] - roots[level - 1]
            for level in range(2, args.max_level + 1)
        }
        for level in range(1, args.max_level + 1):
            print(
                f"{args.sector} boundary root {level}: "
                f"{mp.nstr(roots[level], min(100, args.dps - 5))}"
            )
            if level >= 2:
                print(f"  level_change_{level}={mp.nstr(changes[level], 50)}")
        print(
            "NOTE: exact Schur recursion; numerical roots/residuals are not "
            "interval certificates or a proof of the infinite-level limit."
        )


if __name__ == "__main__":
    main()
