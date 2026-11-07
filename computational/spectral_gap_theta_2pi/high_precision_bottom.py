#!/usr/bin/env python3
"""Resolve the bottom spectral cluster of the local-face gasket operator.

The low cluster at level 5 is too tightly grouped for a short, single-vector
inverse iteration seeded by float64 eigenvectors. This script therefore
refines a three-dimensional invariant subspace for (H - I)^(-1), then
diagonalizes the projected 3x3 matrix in mpmath arithmetic.

The residual and residual^2/gap values printed below are numerical diagnostics,
not interval-arithmetic certificates. The script uses float64 only to seed
the initial three-dimensional subspace and to estimate its separation from
the fourth eigenvalue; all refinement and Ritz calculations use mpmath.
"""
from __future__ import annotations

import time

import numpy as np
from mpmath import mp, mpf, matrix

mp.dps = 80
SUBSPACE_TOL = mpf("1e-20")
CG_TOL = mpf("1e-50")
LEVELS = (2, 3, 4, 5)


def faces(level: int):
    """Return ordered upward faces in the recursive triangular lattice."""
    if level < 0:
        raise ValueError("level must be nonnegative")
    out = [((0, 0), (1, 0), (0, 1))]
    for depth in range(1, level + 1):
        half = 1 << (depth - 1)
        previous = out
        out = [
            tuple((x + dx, y + dy) for x, y in face)
            for dx, dy in ((0, 0), (half, 0), (0, half))
            for face in previous
        ]
    return out


def edge(u, v):
    return (u, v) if u < v else (v, u)


def build(level: int):
    """Build the integer local-face matrix H = D + A_s."""
    vertex_index: dict[tuple[int, int], int] = {}
    edge_sign: dict[tuple[tuple[int, int], tuple[int, int]], int] = {}
    for a, b, c in faces(level):
        for vertex in (a, b, c):
            vertex_index.setdefault(vertex, len(vertex_index))
        for u, v, sign in ((a, b, 1), (a, c, -1), (b, c, -1)):
            edge_sign[edge(u, v)] = sign

    n = len(vertex_index)
    H = np.zeros((n, n), dtype=np.int64)
    for (u, v), sign in edge_sign.items():
        i, j = vertex_index[u], vertex_index[v]
        H[i, j] = H[j, i] = sign
        H[i, i] += 1
        H[j, j] += 1

    if not np.array_equal(H, H.T):
        raise ArithmeticError("constructed matrix is not symmetric")
    rows = [
        [(int(j), int(H[i, j])) for j in np.nonzero(H[i])[0]]
        for i in range(n)
    ]
    # The proved lower bound H >= I makes H-I positive semidefinite.
    # Its diagonal is strictly positive here, enabling Jacobi-preconditioned CG.
    diagonal = [int(H[i, i]) - 1 for i in range(n)]
    if min(diagonal) <= 0:
        raise ArithmeticError("H-I has a nonpositive Jacobi diagonal")
    return H, rows, diagonal


def dot(x, y):
    return mp.fsum(a * b for a, b in zip(x, y))


def norm(x):
    return mp.sqrt(dot(x, x))


def h_matvec(rows, x):
    return [mp.fsum(mpf(a) * x[j] for j, a in row) for row in rows]


def shifted_matvec(rows, x):
    hx = h_matvec(rows, x)
    return [hx[i] - x[i] for i in range(len(x))]  # (H-I)x


def orthonormalize(vectors):
    """Modified Gram-Schmidt with a second re-orthogonalization pass."""
    basis = []
    for original in vectors:
        vector = original[:]
        for _ in range(2):
            for q in basis:
                coefficient = dot(q, vector)
                vector = [
                    vector[i] - coefficient * q[i] for i in range(len(vector))
                ]
        length = norm(vector)
        if length == 0:
            raise ArithmeticError("block vectors lost rank")
        basis.append([value / length for value in vector])
    return basis


def pcg_solve_h_minus_i(rows, diagonal, rhs, tol=CG_TOL, max_iter=700):
    """Diagonally preconditioned CG for (H-I)x=rhs."""
    x = [mpf(0)] * len(rhs)
    residual = rhs[:]
    rhs_norm = norm(rhs)
    if rhs_norm == 0:
        return x, 0

    z = [residual[i] / diagonal[i] for i in range(len(rhs))]
    direction = z[:]
    rz = dot(residual, z)
    for iteration in range(1, max_iter + 1):
        product = shifted_matvec(rows, direction)
        curvature = dot(direction, product)
        if curvature <= 0:
            raise ArithmeticError("CG encountered nonpositive curvature")
        alpha = rz / curvature
        x = [x[i] + alpha * direction[i] for i in range(len(rhs))]
        residual = [
            residual[i] - alpha * product[i] for i in range(len(rhs))
        ]
        if norm(residual) <= tol * rhs_norm:
            return x, iteration
        z = [residual[i] / diagonal[i] for i in range(len(rhs))]
        rz_new = dot(residual, z)
        beta = rz_new / rz
        direction = [z[i] + beta * direction[i] for i in range(len(rhs))]
        rz = rz_new
    raise RuntimeError("CG did not reach its requested relative residual")


def projected_matrix(basis, rows):
    """Return the 3x3 Rayleigh-Ritz matrix and block residual norm."""
    h_basis = [h_matvec(rows, q) for q in basis]
    projected = matrix(3, 3)
    for i in range(3):
        for j in range(3):
            projected[i, j] = dot(basis[i], h_basis[j])
    residual_entries = []
    for j in range(3):
        residual_entries.extend(
            h_basis[j][k]
            - mp.fsum(basis[i][k] * projected[i, j] for i in range(3))
            for k in range(len(basis[j]))
        )
    return projected, norm(residual_entries)


def high_precision_low_cluster(level: int):
    started = time.time()
    H, rows, diagonal = build(level)
    n = H.shape[0]

    # Float64 is only an initializer; the block is subsequently refined in MP.
    float_eigenvalues, float_eigenvectors = np.linalg.eigh(H.astype(np.float64))
    basis = orthonormalize([
        [mpf(float(value)) for value in float_eigenvectors[:, column]]
        for column in range(3)
    ])
    projected, block_residual = projected_matrix(basis, rows)
    total_cg_iterations = 0
    outer_iterations = 0

    while block_residual >= SUBSPACE_TOL and outer_iterations < 40:
        refined = []
        for vector in basis:
            solution, cg_iterations = pcg_solve_h_minus_i(rows, diagonal, vector)
            total_cg_iterations += cg_iterations
            refined.append(solution)
        basis = orthonormalize(refined)
        projected, block_residual = projected_matrix(basis, rows)
        outer_iterations += 1

    if block_residual >= SUBSPACE_TOL:
        raise RuntimeError(
            f"level {level}: block residual {mp.nstr(block_residual, 8)} "
            f"did not reach {mp.nstr(SUBSPACE_TOL, 4)}"
        )

    eigenvalues, eigenvectors = mp.eigsy(projected)
    # This float64 estimate is intentionally reported only as a diagnostic.
    separation_estimate = mpf(float(float_eigenvalues[3])) - eigenvalues[2]
    error_scale = (
        block_residual**2 / separation_estimate
        if separation_estimate > 0 else mp.nan
    )
    eigen_residuals = []
    for column in range(3):
        vector = [
            mp.fsum(basis[i][k] * eigenvectors[i, column] for i in range(3))
            for k in range(n)
        ]
        h_vector = h_matvec(rows, vector)
        rayleigh = dot(vector, h_vector)
        eigen_residuals.append(norm([
            h_vector[k] - rayleigh * vector[k] for k in range(n)
        ]))

    return {
        "level": level,
        "vertices": n,
        "eigenvalues": [eigenvalues[i] for i in range(3)],
        "block_residual": block_residual,
        "separation_estimate": separation_estimate,
        "error_scale": error_scale,
        "eigen_residuals": eigen_residuals,
        "outer_iterations": outer_iterations,
        "cg_iterations": total_cg_iterations,
        "seconds": time.time() - started,
    }


def main():
    results = {}
    for level in LEVELS:
        result = high_precision_low_cluster(level)
        results[level] = result
        values = result["eigenvalues"]
        print(
            f"level {level}: n={result['vertices']} "
            f"lambda_min={mp.nstr(values[0], 50)}"
        )
        print(
            f"  next={mp.nstr(values[1], 40)}; "
            f"third={mp.nstr(values[2], 40)}"
        )
        if level == 5:
            print(
                "  bottom-to-next splitting="
                f"{mp.nstr(values[1] - values[0], 18)}"
            )
        print(
            f"  block_residual={mp.nstr(result['block_residual'], 9)}; "
            f"separation_estimate={mp.nstr(result['separation_estimate'], 10)}; "
            f"residual^2/separation={mp.nstr(result['error_scale'], 9)}"
        )
        print(
            "  individual_residuals="
            + ", ".join(mp.nstr(value, 8) for value in result["eigen_residuals"])
        )
        print(
            f"  outer_iterations={result['outer_iterations']}; "
            f"CG_iterations={result['cg_iterations']}; "
            f"elapsed={result['seconds']:.2f}s",
            flush=True,
        )

    # delta_m = lambda_m - lambda_(m-1), so all increments are positive.
    deltas = {
        level: results[level]["eigenvalues"][0]
        - results[level - 1]["eigenvalues"][0]
        for level in (3, 4, 5)
    }
    for level in (4, 5):
        ratio = deltas[level] / deltas[level - 1] ** 2
        print(
            f"delta_{level}={mp.nstr(deltas[level], 35)}; "
            f"delta_{level}/delta_{level - 1}^2={mp.nstr(ratio, 35)}"
        )

    coefficient = deltas[5] / deltas[4] ** 2
    predicted_delta_6 = coefficient * deltas[5] ** 2
    print(
        "conditional_delta_6_extrapolation="
        f"{mp.nstr(predicted_delta_6, 35)}"
    )
    print(
        "conditional_lambda_infinity_estimate="
        f"{mp.nstr(results[5]['eigenvalues'][0] + predicted_delta_6, 45)}"
    )
    print("NOTE: extrapolation is empirical, not a proof or interval certificate.")


if __name__ == "__main__":
    main()
