#!/usr/bin/env python3
"""High-precision symmetry-sector resolution of the local-face bottom spectrum.

The unsigned signless Laplacian Q = D + A is unitarily equivalent to the
local-face signed operator H = D + A_s by the exact row gauge already proved
in Lean. Q commutes with the S3 action permuting the three barycentric corner
coordinates. Its low cluster is resolved into the fully symmetric A1 sector
and one complex C3-character sector (the two conjugate copies form the
two-dimensional E representation).

Float64 is used for graph assembly, the starting eigensolver, and sparse
SuperLU factorization. The mixed-precision path applies those sparse L/U
factors with mpmath forward/back substitution and iterative refinement;
quotient matrix-vector products, Rayleigh quotients, and residuals are also
computed in mpmath. Residuals are diagnostics, not interval certificates.
"""
from __future__ import annotations

import argparse
import itertools
import time

import numpy as np
import scipy.sparse as sp
from scipy.sparse.linalg import eigsh, splu
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



def build_a1_quotient_sparse(level: int):
    """Build K = Q_A1-I as sparse rows without an O(n_orbits^2) count table."""
    vertices, index, neighbors, degree, Q = build_graph(level)
    side = 1 << level
    vertex_set = set(vertices)
    seen = set()
    orbits = []
    for vertex in vertices:
        if vertex in seen:
            continue
        orbit = s3_orbit(vertex, side)
        if not orbit <= vertex_set:
            raise ArithmeticError("the S3 action does not preserve the vertex set")
        seen.update(orbit)
        orbits.append(sorted(orbit))
    if seen != vertex_set:
        raise ArithmeticError("S3 orbit partition missed graph vertices")

    orbit_index = {
        vertex: orbit_id
        for orbit_id, orbit in enumerate(orbits)
        for vertex in orbit
    }
    sizes = [len(orbit) for orbit in orbits]
    orbit_degree = []
    counts_by_orbit = []

    for orbit_id, orbit in enumerate(orbits):
        reference = None
        for vertex in orbit:
            counts = {}
            ui = index[vertex]
            for neighbor_index in neighbors[ui]:
                target_orbit = orbit_index[vertices[neighbor_index]]
                counts[target_orbit] = counts.get(target_orbit, 0) + 1
            if reference is None:
                reference = counts
            elif reference != counts:
                raise ArithmeticError(
                    f"orbit partition is not equitable at level {level}, orbit {orbit_id}"
                )
        counts_by_orbit.append(reference)
        orbit_degree.append(degree[index[orbit[0]]])

    rows = []
    float_rows, float_cols, float_data = [], [], []
    for a, counts in enumerate(counts_by_orbit):
        # The diagonal exists even when an orbit has no internal neighbors.
        diagonal = mpf(orbit_degree[a] + counts.get(a, 0) - 1)
        row = [(a, diagonal)]
        float_rows.append(a)
        float_cols.append(a)
        float_data.append(float(diagonal))
        for b, multiplicity in sorted(counts.items()):
            if b == a:
                continue
            value = mpf(multiplicity) * mp.sqrt(mpf(sizes[a]) / sizes[b])
            if value != 0:
                row.append((b, value))
                float_rows.append(a)
                float_cols.append(b)
                float_data.append(float(value))
        rows.append(row)

    row_dicts = [dict(row) for row in rows]
    asymmetry = mpf(0)
    for i, row in enumerate(row_dicts):
        for j, value in row.items():
            asymmetry = max(
                asymmetry,
                abs(value - row_dicts[j].get(i, mpf(0))),
            )
    if asymmetry > mpf("1e-60"):
        raise ArithmeticError(f"A1 sparse quotient is not symmetric: {asymmetry}")
    if any(dict(row).get(i, mpf(0)) <= 0 for i, row in enumerate(rows)):
        raise ArithmeticError("A1 shifted quotient has a nonpositive diagonal")

    K_float = sp.coo_matrix(
        (
            np.asarray(float_data, dtype=np.float64),
            (float_rows, float_cols),
        ),
        shape=(len(orbits), len(orbits)),
    ).tocsr()
    return rows, K_float, Q, len(vertices), len(orbits), asymmetry


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



def build_a2_quotient(level: int):
    """Build Q-I on the alternating S3 representation (the A2 sector).

    Alternating functions vanish on vertices with two equal barycentric
    coordinates. Every remaining S3 orbit has size six, so its normalized
    signed-orbit basis has the same normalization on every orbit.
    """
    vertices, index, neighbors, degree, _ = build_graph(level)
    side = 1 << level
    orbit_data = {}
    for vertex in vertices:
        coordinates = (vertex[0], vertex[1], side - vertex[0] - vertex[1])
        ordered = tuple(sorted(coordinates))
        if len(set(ordered)) != 3:
            continue
        permutation = [ordered.index(value) for value in coordinates]
        inversions = sum(
            permutation[i] > permutation[j]
            for i in range(3) for j in range(i + 1, 3)
        )
        sign = -1 if inversions % 2 else 1
        orbit_data[vertex] = (ordered, sign)

    representatives = sorted({data[0] for data in orbit_data.values()})
    orbit_index = {representative: i for i, representative in enumerate(representatives)}
    vertex_orbit = {
        vertex: (orbit_index[representative], sign)
        for vertex, (representative, sign) in orbit_data.items()
    }

    dimension = len(representatives)
    K = matrix(dimension, dimension)
    for p, representative in enumerate(representatives):
        # The canonical representative is the vertex with sorted barycentric
        # coordinates. Reflection-fixed neighbors have zero A2 component.
        u = (representative[0], representative[1])
        ui = index[u]
        K[p, p] = degree[ui] - 1
        for neighbor_index in neighbors[ui]:
            neighbor = vertices[neighbor_index]
            orbit_entry = vertex_orbit.get(neighbor)
            if orbit_entry is None:
                continue
            q, sign = orbit_entry
            K[p, q] += sign

    asymmetry = max(
        abs(K[i, j] - K[j, i])
        for i in range(dimension) for j in range(dimension)
    )
    if asymmetry > mpf("1e-60"):
        raise ArithmeticError(f"A2 quotient is not symmetric: {asymmetry}")
    if min(K[i, i] for i in range(dimension)) <= 0:
        raise ArithmeticError("A2 shifted quotient has a nonpositive diagonal")

    K_float = np.array(
        [[float(K[i, j]) for j in range(dimension)] for i in range(dimension)],
        dtype=np.float64,
    )
    return K, K_float, len(vertices), dimension


def a2_bottom(level: int, iterations: int = 40):
    """High-precision inverse iteration for the alternating S3 (A2) sector."""
    started = time.time()
    K, K_float, full_n, sector_n = build_a2_quotient(level)
    _, vectors = np.linalg.eigh(K_float)
    v = matrix([mpf(float(value)) for value in vectors[:, 0]])
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
        "sector_dimension": sector_n,
        "iterations": iterations,
        "seconds": time.time() - started,
    }




def multiprecision_lu_solver(lu, dimension: int, complex_mode: bool):
    """Solve with SuperLU's sparse L/U factors using mpmath substitutions.

    SuperLU computes a float64 factorization. Reusing its L/U factors in
    multiple-precision forward/back substitution avoids rounding every
    correction back to float64, which otherwise stalls iterative refinement
    near machine precision.
    """
    lower = lu.L.tocsr()
    upper = lu.U.tocsr()

    def convert(value):
        if complex_mode:
            return mp.mpc(float(np.real(value)), float(np.imag(value)))
        return mpf(float(value))

    lower_rows = []
    upper_rows = []
    for i in range(dimension):
        lower_rows.append([
            (int(lower.indices[k]), convert(lower.data[k]))
            for k in range(lower.indptr[i], lower.indptr[i + 1])
        ])
        upper_rows.append([
            (int(upper.indices[k]), convert(upper.data[k]))
            for k in range(upper.indptr[i], upper.indptr[i + 1])
        ])

    # SuperLU's identity is A[inv(perm_r), :][:, inv(perm_c)] = L * U.
    inverse_row_permutation = np.argsort(lu.perm_r)
    inverse_column_permutation = np.argsort(lu.perm_c)
    zero = mp.mpc(0) if complex_mode else mpf(0)

    def solve(rhs):
        permuted_rhs = [rhs[int(i)] for i in inverse_row_permutation]
        forward = [zero for _ in range(dimension)]
        for i, row in enumerate(lower_rows):
            subtotal = zero
            diagonal = None
            for j, coefficient in row:
                if j < i:
                    subtotal += coefficient * forward[j]
                elif j == i:
                    diagonal = coefficient
            if diagonal is None or abs(diagonal) == 0:
                raise ArithmeticError(f"zero diagonal in SuperLU L factor at row {i}")
            forward[i] = (permuted_rhs[i] - subtotal) / diagonal

        permuted_solution = [zero for _ in range(dimension)]
        for i in range(dimension - 1, -1, -1):
            subtotal = zero
            diagonal = None
            for j, coefficient in upper_rows[i]:
                if j > i:
                    subtotal += coefficient * permuted_solution[j]
                elif j == i:
                    diagonal = coefficient
            if diagonal is None or abs(diagonal) == 0:
                raise ArithmeticError(f"zero diagonal in SuperLU U factor at row {i}")
            permuted_solution[i] = (forward[i] - subtotal) / diagonal

        solution = [zero for _ in range(dimension)]
        for i, original_index in enumerate(inverse_column_permutation):
            solution[int(original_index)] = permuted_solution[i]
        return solution

    return solve


def mixed_precision_bottom(
    level: int,
    sector: str,
    iterations: int = 110,
    dps: int = 110,
    solve_digits: int | None = None,
    progress_every: int = 0,
):
    """Resolve a sector bottom with sparse-LU preconditioning and MP refinement.

    SuperLU supplies a sparse float64 factorization. Its L/U factors are then
    applied by mpmath forward/back substitution, so every iterative-refinement
    correction is accumulated at the requested precision rather than rounded
    back to float64. Matrix-vector products and Rayleigh diagnostics are also MP.
    """
    started = time.time()
    sector = sector.upper()
    if sector not in {"A1", "A2", "E"}:
        raise ValueError("sector must be one of A1, A2, or E")
    if iterations < 1 or dps < 50:
        raise ValueError("iterations must be positive and dps must be at least 50")
    if progress_every < 0:
        raise ValueError("progress_every must be nonnegative")
    if solve_digits is None:
        solve_digits = dps - 15
    if not 30 <= solve_digits < dps:
        raise ValueError("solve_digits must be at least 30 and less than dps")

    with mp.workdps(dps):
        print(
            f"mixed {sector} level {level}: assembling graph/quotient "
            f"(dps={dps}, solve_digits={solve_digits}, iterations={iterations})",
            flush=True,
        )
        if sector == "A1":
            (
                rows,
                K_float,
                _full_graph,
                full_n,
                sector_n,
                _asymmetry,
            ) = build_a1_quotient_sparse(level)
            matrix_for_factor = K_float.tocsc()
            seed_matrix = K_float
            complex_mode = False
        elif sector == "A2":
            K_mp, K_float, full_n, sector_n = build_a2_quotient(level)
            matrix_for_factor = sp.csc_matrix(K_float)
            seed_matrix = matrix_for_factor
            complex_mode = False
            rows = [
                [(j, K_mp[i, j]) for j in range(sector_n) if K_mp[i, j] != 0]
                for i in range(sector_n)
            ]
        else:
            rows, _diagonal, K_float, _full_graph, full_n, sector_n = build_e_sector(level)
            # build_e_sector returns Q_sector for the float64 seed eigensolver,
            # while rows represent Q_sector - I for inverse iteration.
            seed_matrix = K_float
            matrix_for_factor = (K_float - sp.eye(sector_n, format="csr")).tocsc()
            complex_mode = True

        if matrix_for_factor.shape != (sector_n, sector_n):
            raise ArithmeticError("sector matrix has an unexpected shape")

        print(
            f"mixed {sector} level {level}: factoring sparse shifted matrix "
            f"of dimension {sector_n}",
            flush=True,
        )
        factor_started = time.time()
        lu = splu(matrix_for_factor)
        solve_lu = multiprecision_lu_solver(lu, sector_n, complex_mode)
        print(
            f"mixed {sector} level {level}: sparse LU ready in "
            f"{time.time() - factor_started:.1f}s",
            flush=True,
        )
        if sector_n <= 4:
            # ARPACK requires k < N. The smallest regression levels have
            # quotient dimension four, so use a dense seed eigensolve there.
            _float_values, float_vectors = np.linalg.eigh(seed_matrix.toarray())
        else:
            _float_values, float_vectors = eigsh(
                seed_matrix, k=min(4, sector_n - 1), which="SA", tol=1e-13
            )
        seed = float_vectors[:, int(np.argmin(_float_values))]
        if complex_mode:
            vector = [
                mp.mpc(float(value.real), float(value.imag)) for value in seed
            ]
        else:
            vector = [mpf(float(value)) for value in seed]

        vector_norm = complex_norm
        vector = [value / vector_norm(vector) for value in vector]

        solve_tolerance = mp.power(10, -solve_digits)
        # A float64 LU preconditioner typically contributes about 15 digits
        # per refinement step. Scale the cap with the requested solve accuracy,
        # with extra headroom for conditioning and nonuniform pivot growth.
        max_corrections = max(12, (solve_digits + 7) // 8 + 4)
        max_correction_rounds = 0
        max_linear_residual = mpf(0)

        def refined_solve(rhs):
            rhs_norm = vector_norm(rhs)
            solution = solve_lu(rhs)
            relative_residual = mpf(1)
            correction_rounds = 0
            for correction_rounds in range(max_corrections + 1):
                product = [
                    mp.fsum(coefficient * solution[j] for j, coefficient in row)
                    for row in rows
                ]
                residual = [rhs[i] - product[i] for i in range(sector_n)]
                relative_residual = vector_norm(residual) / rhs_norm
                if relative_residual < solve_tolerance:
                    break
                if correction_rounds == max_corrections:
                    raise RuntimeError(
                        "multiprecision LU refinement stalled at relative residual "
                        + mp.nstr(relative_residual, 8)
                    )
                correction = solve_lu(residual)
                solution = [
                    solution[i] + correction[i] for i in range(sector_n)
                ]
            return solution, relative_residual, correction_rounds

        for iteration in range(1, iterations + 1):
            solution, linear_residual, correction_rounds = refined_solve(vector)
            max_linear_residual = max(max_linear_residual, linear_residual)
            max_correction_rounds = max(max_correction_rounds, correction_rounds)
            solution_norm = vector_norm(solution)
            vector = [value / solution_norm for value in solution]
            if progress_every and (
                iteration % progress_every == 0 or iteration == iterations
            ):
                progress_product = [
                    mp.fsum(coefficient * vector[j] for j, coefficient in row)
                    for row in rows
                ]
                progress_ritz = real_inner(vector, progress_product)
                progress_residual = vector_norm([
                    progress_product[i] - progress_ritz * vector[i]
                    for i in range(sector_n)
                ])
                print(
                    f"mixed {sector} level {level}: iteration {iteration}/{iterations} "
                    f"lambda={mp.nstr(progress_ritz + 1, 70)} "
                    f"residual={mp.nstr(progress_residual, 6)} "
                    f"linear_residual={mp.nstr(max_linear_residual, 6)}",
                    flush=True,
                )

        product = [
            mp.fsum(coefficient * vector[j] for j, coefficient in row)
            for row in rows
        ]
        ritz_value = real_inner(vector, product)
        residual = vector_norm(
            [product[i] - ritz_value * vector[i] for i in range(sector_n)]
        )

        return {
            "level": level,
            "sector": sector,
            "lambda": ritz_value + 1,
            "residual": residual,
            "linear_residual": max_linear_residual,
            "full_dimension": full_n,
            "sector_dimension": sector_n,
            "iterations": iterations,
            "dps": dps,
            "solve_digits": solve_digits,
            "correction_rounds": max_correction_rounds,
            "seconds": time.time() - started,
        }




def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--a1-iterations", type=int, default=60)
    parser.add_argument("--e-iterations", type=int, default=50)
    parser.add_argument(
        "--mixed-precision-levels",
        type=int,
        nargs="+",
        default=[],
        help="optional levels for sparse-LU/multiprecision refinement",
    )
    parser.add_argument(
        "--mixed-precision-sectors",
        choices=("A1", "A2", "E"),
        nargs="+",
        default=("A1", "E"),
        help="sectors to compute when --mixed-precision-levels is supplied",
    )
    parser.add_argument("--mixed-precision-dps", type=int, default=110)
    parser.add_argument("--mixed-precision-solve-digits", type=int, default=None)
    parser.add_argument("--mixed-precision-iterations", type=int, default=110)
    parser.add_argument("--mixed-precision-progress-every", type=int, default=0)
    parser.add_argument(
        "--mixed-precision-only",
        action="store_true",
        help="skip the standard level-2-to-6 diagnostics and run only requested sectors",
    )
    args = parser.parse_args()

    if args.mixed_precision_only:
        if not args.mixed_precision_levels:
            parser.error("--mixed-precision-only requires --mixed-precision-levels")
        for level in args.mixed_precision_levels:
            for sector in args.mixed_precision_sectors:
                result = mixed_precision_bottom(
                    level,
                    sector,
                    iterations=args.mixed_precision_iterations,
                    dps=args.mixed_precision_dps,
                    solve_digits=args.mixed_precision_solve_digits,
                    progress_every=args.mixed_precision_progress_every,
                )
                print(
                    f"mixed {sector} level {level}: "
                    f"n={result['full_dimension']} "
                    f"sector_n={result['sector_dimension']} "
                    f"lambda={mp.nstr(result['lambda'], 320)} "
                    f"residual={mp.nstr(result['residual'], 12)} "
                    f"linear_residual={mp.nstr(result['linear_residual'], 12)} "
                    f"solve_digits={result['solve_digits']} "
                    f"correction_rounds={result['correction_rounds']} "
                    f"elapsed={result['seconds']:.2f}s",
                    flush=True,
                )
        return

    results_a1 = {}
    for level in (2, 3, 4, 5, 6):
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

    results_a2 = {}
    for level in (5, 6):
        result = a2_bottom(level)
        results_a2[level] = result
        print(
            f"A2 level {level}: n={result['full_dimension']} "
            f"sector_n={result['sector_dimension']} "
            f"lambda={mp.nstr(result['lambda'], 60)} "
            f"residual={mp.nstr(result['residual'], 8)} "
            f"elapsed={result['seconds']:.2f}s",
            flush=True,
        )

    deltas = {
        level: results_a1[level]["lambda"] - results_a1[level - 1]["lambda"]
        for level in (3, 4, 5, 6)
    }
    ratios = {
        level: deltas[level] / deltas[level - 1] ** 2
        for level in (4, 5, 6)
    }
    splitting5 = results_e[5]["lambda"] - results_a1[5]["lambda"]
    splitting6 = results_e[6]["lambda"] - results_a1[6]["lambda"]
    predicted_delta7 = ratios[6] * deltas[6] ** 2
    conditional_limit = results_a1[6]["lambda"] + predicted_delta7

    for level in (3, 4, 5, 6):
        print(f"delta_{level}={mp.nstr(deltas[level], 45)}")
    for level in (4, 5, 6):
        print(
            f"delta_{level}/delta_{level - 1}^2="
            f"{mp.nstr(ratios[level], 35)}"
        )
    print(f"A1_E_splitting_5={mp.nstr(splitting5, 35)}")
    print(f"A1_E_splitting_6={mp.nstr(splitting6, 35)}")
    print(f"conditional_delta_7={mp.nstr(predicted_delta7, 35)}")
    print(f"conditional_limit_estimate={mp.nstr(conditional_limit, 50)}")
    print("NOTE: empirical extrapolation only; residuals are not interval certificates.")

    for level in args.mixed_precision_levels:
        for sector in args.mixed_precision_sectors:
            result = mixed_precision_bottom(
                level,
                sector,
                iterations=args.mixed_precision_iterations,
                dps=args.mixed_precision_dps,
                solve_digits=args.mixed_precision_solve_digits,
                progress_every=args.mixed_precision_progress_every,
            )
            print(
                f"mixed {sector} level {level}: "
                f"n={result['full_dimension']} "
                f"sector_n={result['sector_dimension']} "
                f"lambda={mp.nstr(result['lambda'], 90)} "
                f"residual={mp.nstr(result['residual'], 8)} "
                f"linear_residual={mp.nstr(result['linear_residual'], 8)} "
                f"solve_digits={result['solve_digits']} "
                f"correction_rounds={result['correction_rounds']} "
                f"elapsed={result['seconds']:.2f}s",
                flush=True,
            )

    for level in (5, 6):
        diagnostic = full_low_cluster_diagnostic(results_a1[level]["full_Q"])
        print(
            f"full_float64_low_cluster_level_{level}="
            + ", ".join(f"{x:.15g}" for x in diagnostic)
        )


if __name__ == "__main__":
    main()
