#!/usr/bin/env python3
"""High-precision symmetry-sector resolution of the local-face bottom spectrum.

The unsigned signless Laplacian Q = D + A is unitarily equivalent to the
local-face signed operator H = D + A_s by the exact row gauge already proved
in Lean. Q commutes with the S3 action permuting the three barycentric corner
coordinates. Its low cluster is resolved into the fully symmetric A1 sector
and one complex C3-character sector (the two conjugate copies form the
two-dimensional E representation).

Float64 is used only to seed inverse iteration. The quotient matrices,
factorization / preconditioned CG solves, Rayleigh quotients, and residuals
are computed with mpmath. Residuals are diagnostics, not interval certificates.
"""
from __future__ import annotations

import argparse
import itertools
import time

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh
from mpmath import mp, mpf, matrix

mp.dps = 75
CG_TOL = mpf("1e-55")


def faces(level: int):
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


def build_graph(level: int):
    """Construct the unweighted graph and signless Laplacian Q = D + A."""
    vertices = {}
    edges = set()
    for a, b, c in faces(level):
        for v in (a, b, c):
            vertices.setdefault(v, len(vertices))
        edges.update((edge(a, b), edge(a, c), edge(b, c)))

    ordered = list(vertices)
    index = {v: i for i, v in enumerate(ordered)}
    neighbors = [[] for _ in ordered]
    rows, cols, data = [], [], []
    degree = [0] * len(ordered)
    for u, v in sorted(edges):
        i, j = index[u], index[v]
        neighbors[i].append(j)
        neighbors[j].append(i)
        rows.extend((i, j))
        cols.extend((j, i))
        data.extend((1, 1))
        degree[i] += 1
        degree[j] += 1
    rows.extend(range(len(ordered)))
    cols.extend(range(len(ordered)))
    data.extend(degree)
    Q = sp.coo_matrix(
        (np.asarray(data, dtype=np.float64), (rows, cols)),
        shape=(len(ordered), len(ordered)),
    ).tocsr()
    return ordered, index, neighbors, degree, Q


def s3_orbit(v, side):
    i, j = v
    k = side - i - j
    return {
        (p[0], p[1])
        for p in itertools.permutations((i, j, k))
    }


def build_a1_quotient(level: int):
    """Build the normalized quotient on functions invariant under all S3."""
    vertices, index, neighbors, degree, Q = build_graph(level)
    side = 1 << level
    vertex_set = set(vertices)
    seen = set()
    orbits = []
    for v in vertices:
        if v in seen:
            continue
        orbit = s3_orbit(v, side)
        if not orbit <= vertex_set:
            raise ArithmeticError("the S3 action does not preserve the vertex set")
        seen.update(orbit)
        orbits.append(sorted(orbit))
    if seen != vertex_set:
        raise ArithmeticError("S3 orbit partition missed graph vertices")

    orbit_index = {
        v: a for a, orbit in enumerate(orbits) for v in orbit
    }
    sizes = [len(orbit) for orbit in orbits]
    count = [[0] * len(orbits) for _ in orbits]
    orbit_degree = []
    for a, orbit in enumerate(orbits):
        reference = None
        for u in orbit:
            row_counts = [0] * len(orbits)
            ui = index[u]
            for vj in neighbors[ui]:
                row_counts[orbit_index[vertices[vj]]] += 1
            if reference is None:
                reference = row_counts
            elif reference != row_counts:
                raise ArithmeticError(
                    f"orbit partition is not equitable at level {level}, orbit {a}"
                )
        count[a] = reference
        orbit_degree.append(degree[index[orbit[0]]])

    n = len(orbits)
    # Build K = Q_A1 - I in arbitrary precision. The normalized orbit
    # indicator basis gives off-diagonal entries C_ab * sqrt(|O_a|/|O_b|).
    K = matrix(n, n)
    K_float = np.zeros((n, n), dtype=np.float64)
    for a in range(n):
        for b in range(n):
            if a == b:
                value = mpf(orbit_degree[a] + count[a][a] - 1)
            elif count[a][b]:
                value = mpf(count[a][b]) * mp.sqrt(mpf(sizes[a]) / sizes[b])
            else:
                value = mpf(0)
            K[a, b] = value
            K_float[a, b] = float(value)

    asymmetry = max(
        abs(K[a, b] - K[b, a]) for a in range(n) for b in range(n)
    )
    if asymmetry > mpf("1e-60"):
        raise ArithmeticError(f"A1 quotient is not symmetric: {asymmetry}")
    if min(K[a, a] for a in range(n)) <= 0:
        raise ArithmeticError("A1 shifted quotient has a nonpositive diagonal")
    return K, K_float, Q, len(vertices), len(orbits)


def a1_bottom(level: int, iterations: int = 60):
    """High-precision inverse iteration in the fully symmetric A1 sector."""
    started = time.time()
    K, K_float, full_Q, full_n, quotient_n = build_a1_quotient(level)
    values, vectors = np.linalg.eigh(K_float)
    v = matrix([mpf(float(x)) for x in vectors[:, 0]])
    LU, pivots = mp.LU_decomp(K)
    for _ in range(iterations):
        y = mp.L_solve(LU, v, pivots)
        v = mp.U_solve(LU, y)
        v /= mp.norm(v)

    Kv = K * v
    nu = (v.T * Kv)[0]
    residual = mp.norm(Kv - nu * v)
    return {
        "level": level,
        "lambda": nu + 1,
        "residual": residual,
        "full_dimension": full_n,
        "sector_dimension": quotient_n,
        "iterations": iterations,
        "seconds": time.time() - started,
        "full_Q": full_Q,
    }


def rotate(v, side):
    i, j = v
    k = side - i - j
    return (j, k)


def build_e_sector(level: int):
    """Build sparse K = Q_(C3,omega) - I in a complex Fourier basis."""
    vertices, index, neighbors, degree, Q = build_graph(level)
    side = 1 << level
    seen = set()
    representatives = []
    orbit_map = {}
    for v in vertices:
        if v in seen:
            continue
        cycle = [v, rotate(v, side), rotate(rotate(v, side), side)]
        if len(set(cycle)) != 3:
            raise ArithmeticError("unexpected C3-fixed vertex")
        q = len(representatives)
        representatives.append(v)
        for t, w in enumerate(cycle):
            orbit_map[w] = (q, t)
            seen.add(w)
    if len(representatives) * 3 != len(vertices):
        raise ArithmeticError("C3 orbits do not partition the vertices")

    omega = mp.mpc(mpf("-0.5"), mp.sqrt(3) / 2)
    rows = []
    diagonal = []
    float_rows, float_cols, float_data = [], [], []
    for p, u in enumerate(representatives):
        ui = index[u]
        accum = {p: mpf(degree[ui])}
        for vj in neighbors[ui]:
            q, t = orbit_map[vertices[vj]]
            accum[q] = accum.get(q, mp.mpc(0)) + omega**t
        # Shift the diagonal by one: the inverse iteration is for Q_sector-I.
        accum[p] = accum[p] - 1
        accum = {q: value for q, value in accum.items() if abs(value) > mpf("1e-65")}
        rows.append(list(accum.items()))
        diagonal_value = accum.get(p, mp.mpc(0))
        if abs(mp.im(diagonal_value)) > mpf("1e-60"):
            raise ArithmeticError("C3-sector diagonal is not real")
        diagonal.append(mp.re(diagonal_value))
        for q, value in accum.items():
            float_rows.append(p)
            float_cols.append(q)
            float_data.append(complex(float(mp.re(value)), float(mp.im(value))))

    if min(diagonal) <= 0:
        raise ArithmeticError("C3 shifted sector has a nonpositive Jacobi diagonal")

    # A high-precision Hermitian check catches phase/orbit-order errors.
    row_dicts = [dict(row) for row in rows]
    hermitian_error = mpf(0)
    for i, row in enumerate(row_dicts):
        for j, value in row.items():
            reverse = row_dicts[j].get(i, mp.mpc(0))
            hermitian_error = max(hermitian_error, abs(value - mp.conj(reverse)))
    if hermitian_error > mpf("1e-60"):
        raise ArithmeticError(f"C3 sector is not Hermitian: {hermitian_error}")

    K_float = sp.coo_matrix(
        (np.asarray(float_data, dtype=np.complex128), (float_rows, float_cols)),
        shape=(len(representatives), len(representatives)),
    ).tocsr()
    # Restore I only for the float64 starting eigensolver; eigenvectors are
    # identical for K and K+I.
    K_float = K_float + sp.eye(len(representatives), format="csr")
    return rows, diagonal, K_float, Q, len(vertices), len(representatives)


def real_inner(x, y):
    return mp.fsum([
        mp.re(a) * mp.re(b) + mp.im(a) * mp.im(b)
        for a, b in zip(x, y)
    ])


def complex_norm(x):
    return mp.sqrt(real_inner(x, x))


def sparse_complex_matvec(rows, x):
    return [
        mp.fsum([coefficient * x[j] for j, coefficient in row])
        for row in rows
    ]


def pcg_hermitian(rows, diagonal, rhs, tol=CG_TOL, max_iter=900):
    """Jacobi-preconditioned CG for a Hermitian positive-definite sector."""
    x = [mp.mpc(0) for _ in rhs]
    residual = rhs[:]
    rhs_norm = complex_norm(rhs)
    if rhs_norm == 0:
        return x, 0

    z = [residual[i] / diagonal[i] for i in range(len(rhs))]
    direction = z[:]
    rz = real_inner(residual, z)
    for iteration in range(1, max_iter + 1):
        product = sparse_complex_matvec(rows, direction)
        curvature = real_inner(direction, product)
        if curvature <= 0:
            raise ArithmeticError("C3-sector CG encountered nonpositive curvature")
        alpha = rz / curvature
        x = [x[i] + alpha * direction[i] for i in range(len(x))]
        residual = [
            residual[i] - alpha * product[i] for i in range(len(residual))
        ]
        if complex_norm(residual) <= tol * rhs_norm:
            return x, iteration
        z = [residual[i] / diagonal[i] for i in range(len(residual))]
        rz_new = real_inner(residual, z)
        beta = rz_new / rz
        direction = [z[i] + beta * direction[i] for i in range(len(direction))]
        rz = rz_new
    raise RuntimeError("C3-sector CG failed to reach its requested residual")


def e_sector_bottom(level: int, iterations: int = 50):
    """High-precision inverse iteration in one C3-character (E) sector."""
    started = time.time()
    rows, diagonal, K_float, full_Q, full_n, sector_n = build_e_sector(level)
    values, vectors = eigsh(K_float, k=4, which="SA", tol=1e-13)
    v = [
        mp.mpc(float(z.real), float(z.imag))
        for z in vectors[:, int(np.argmin(values))]
    ]
    vnorm = complex_norm(v)
    v = [z / vnorm for z in v]
    total_cg = 0
    for _ in range(iterations):
        y, count = pcg_hermitian(rows, diagonal, v)
        total_cg += count
        ynorm = complex_norm(y)
        v = [z / ynorm for z in y]

    Kv = sparse_complex_matvec(rows, v)
    nu = real_inner(v, Kv)
    residual = complex_norm([Kv[i] - nu * v[i] for i in range(len(v))])
    return {
        "level": level,
        "lambda": nu + 1,
        "residual": residual,
        "full_dimension": full_n,
        "sector_dimension": sector_n,
        "iterations": iterations,
        "cg_iterations": total_cg,
        "seconds": time.time() - started,
        "full_Q": full_Q,
    }


def full_low_cluster_diagnostic(Q):
    values = eigsh(Q, k=4, which="SA", return_eigenvectors=False, tol=1e-13)
    return np.sort(values)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a1-iterations", type=int, default=60)
    parser.add_argument("--e-iterations", type=int, default=50)
    args = parser.parse_args()

    results_a1 = {}
    for level in (4, 5, 6):
        result = a1_bottom(level, args.a1_iterations)
        results_a1[level] = result
        print(
            f"A1 level {level}: n={result['full_dimension']} "
            f"sector_n={result['sector_dimension']} "
            f"lambda={mp.nstr(result['lambda'], 60)} "
            f"residual={mp.nstr(result['residual'], 8)} "
            f"elapsed={result['seconds']:.2f}s",
            flush=True,
        )

    results_e = {}
    for level in (5, 6):
        result = e_sector_bottom(level, args.e_iterations)
        results_e[level] = result
        print(
            f"E level {level}: n={result['full_dimension']} "
            f"sector_n={result['sector_dimension']} "
            f"lambda={mp.nstr(result['lambda'], 60)} "
            f"residual={mp.nstr(result['residual'], 8)} "
            f"CG_iterations={result['cg_iterations']} "
            f"elapsed={result['seconds']:.2f}s",
            flush=True,
        )

    delta5 = results_a1[5]["lambda"] - results_a1[4]["lambda"]
    delta6 = results_a1[6]["lambda"] - results_a1[5]["lambda"]
    ratio5 = delta5 / mpf("1.06331839720311836478e-2")**2
    ratio6 = delta6 / delta5**2
    splitting5 = results_e[5]["lambda"] - results_a1[5]["lambda"]
    splitting6 = results_e[6]["lambda"] - results_a1[6]["lambda"]
    predicted_delta7 = ratio6 * delta6**2
    conditional_limit = results_a1[6]["lambda"] + predicted_delta7

    print(f"delta_5={mp.nstr(delta5, 45)}")
    print(f"delta_6={mp.nstr(delta6, 45)}")
    print(f"delta_5/delta_4^2={mp.nstr(ratio5, 35)}")
    print(f"delta_6/delta_5^2={mp.nstr(ratio6, 35)}")
    print(f"A1_E_splitting_5={mp.nstr(splitting5, 35)}")
    print(f"A1_E_splitting_6={mp.nstr(splitting6, 35)}")
    print(f"conditional_delta_7={mp.nstr(predicted_delta7, 35)}")
    print(f"conditional_limit_estimate={mp.nstr(conditional_limit, 50)}")
    print("NOTE: empirical extrapolation only; residuals are not interval certificates.")

    for level in (5, 6):
        diagnostic = full_low_cluster_diagnostic(results_a1[level]["full_Q"])
        print(
            f"full_float64_low_cluster_level_{level}="
            + ", ".join(f"{x:.15g}" for x in diagnostic)
        )


if __name__ == "__main__":
    main()
