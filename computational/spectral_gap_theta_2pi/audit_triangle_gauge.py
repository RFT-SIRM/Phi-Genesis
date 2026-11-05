#!/usr/bin/env python3
"""Exact combinatorial/gauge audit for the local-face theta=2pi model.

Coordinates are integer triangular-lattice pairs (i,j). Every ordered
upward face (a,b,c) contributes s_ab=+1, s_ac=s_bc=-1 and H=D+A_s.
In phi_genesis.mobius.py convention L=D-A_sigma, this is sigma=-s, i.e.
the GF(2) edge variable x=1 on each first/horizontal face edge (a,b).

The script deliberately compares this local-face signing with the separate
pivot-zero representative produced by mobius_spectrum's hole-boundary solver.
They are not interchangeable: the latter imposes only the listed hole rows.
"""
from __future__ import annotations

import argparse
import math
from collections import Counter


def faces(level: int):
    if level < 0:
        raise ValueError("level must be nonnegative")
    out = [((0, 0), (1, 0), (0, 1))]
    for depth in range(1, level + 1):
        half = 1 << (depth - 1)
        old = out
        out = [
            tuple((x + dx, y + dy) for x, y in face)
            for dx, dy in ((0, 0), (half, 0), (0, half))
            for face in old
        ]
    return out


def edge(u, v):
    return (u, v) if u < v else (v, u)


def graph_from_faces(level: int):
    vertices = set()
    edges = set()
    for a, b, c in faces(level):
        vertices.update((a, b, c))
        edges.update((edge(a, b), edge(a, c), edge(b, c)))
    return vertices, edges


def audit(level: int):
    fs = faces(level)
    edge_sign = {}
    face_incidence = Counter()
    degree = Counter()
    vertices = set()

    for a, b, c in fs:
        for v in (a, b, c):
            vertices.add(v)
            face_incidence[v] += 1
        for u, v, s in ((a, b, 1), (a, c, -1), (b, c, -1)):
            e = edge(u, v)
            assert e not in edge_sign, (level, "edge shared by faces", e)
            edge_sign[e] = s
            degree[u] += 1
            degree[v] += 1
            eps_u = -1 if u[1] % 2 else 1
            eps_v = -1 if v[1] % 2 else 1
            assert s == eps_u * eps_v, (level, "gauge mismatch", e, s)

    assert len(fs) == 3**level
    assert len(edge_sign) == 3**(level + 1)
    assert len(vertices) == (3**(level + 1) + 3) // 2
    assert min(face_incidence.values()) == 1
    assert max(face_incidence.values()) == (1 if level == 0 else 2)
    assert min(degree.values()) == 2
    assert max(degree.values()) == (2 if level == 0 else 4)

    # In repository convention sigma=1-2x and L=D-A_sigma. Here sigma=-s.
    # Compute the actual signed product around each ordered elementary face.
    for a, b, c in fs:
        sigma_ab = -edge_sign[edge(a, b)]
        sigma_bc = -edge_sign[edge(b, c)]
        sigma_ca = -edge_sign[edge(c, a)]
        assert sigma_ab * sigma_bc * sigma_ca == -1
        assert (1 - sigma_ab) // 2 == 1
        assert (1 - sigma_bc) // 2 == 0
        assert (1 - sigma_ca) // 2 == 0

    return vertices, edge_sign, face_incidence, degree


def compare_repository_graph(level: int):
    """Compare exact triangular faces against the project's SG graph builder."""
    from phi_genesis.sg_laplacian import sierpinski_graph

    expected_vertices, expected_edges = graph_from_faces(level)
    vertices, edges, _ = sierpinski_graph(level)
    scale = 1 << level

    def to_lattice(point):
        x, y = point
        j = round(2 * scale * y / math.sqrt(3))
        i = round(scale * x - j / 2)
        x_back = (i + j / 2) / scale
        y_back = (math.sqrt(3) * j / 2) / scale
        assert abs(x - x_back) < 1e-10 and abs(y - y_back) < 1e-10
        return (i, j)

    repo_vertices = {to_lattice(v) for v in vertices}
    repo_edges = {edge(to_lattice(vertices[a]), to_lattice(vertices[b])) for a, b in edges}
    assert expected_vertices == repo_vertices, (
        level, "repository vertex mismatch", len(expected_vertices - repo_vertices),
        len(repo_vertices - expected_vertices)
    )
    assert expected_edges == repo_edges, (
        level, "repository edge mismatch", len(expected_edges - repo_edges),
        len(repo_edges - expected_edges)
    )
    return len(repo_vertices), len(repo_edges)


def signed_laplacian_smallest(n: int, edges, x):
    import scipy.sparse as sp
    from scipy.sparse.linalg import eigsh

    degree = [0] * n
    rows, cols, data = [], [], []
    for k, (a, b) in enumerate(edges):
        sigma = 1 - 2 * int(x[k])
        rows.extend((a, b))
        cols.extend((b, a))
        data.extend((-float(sigma), -float(sigma)))
        degree[a] += 1
        degree[b] += 1
    for v in range(n):
        rows.append(v)
        cols.append(v)
        data.append(float(degree[v]))
    matrix = sp.coo_matrix((data, (rows, cols)), shape=(n, n)).tocsr()
    return float(eigsh(matrix, k=1, which="SA", return_eigenvectors=False,
                       tol=1e-11, maxiter=20000)[0])


def lowest_face_model_eigenvalue(level: int):
    """Numerically check the local-face matrix; not the all-level proof."""
    vertices, edge_sign, _, _ = audit(level)
    ordered_vertices = sorted(vertices)
    index = {v: i for i, v in enumerate(ordered_vertices)}
    coordinate_edges = sorted(edge_sign)
    ordered_edges = [(index[u], index[v]) for u, v in coordinate_edges]
    x = [1 if u[1] == v[1] else 0 for u, v in coordinate_edges]
    lam = signed_laplacian_smallest(len(ordered_vertices), ordered_edges, x)
    assert lam >= 1 - 1e-8, (level, "numerical lower-bound sanity check", lam)
    return len(vertices), lam


def compare_hole_solver(level: int):
    """Compare the local-face x with mobius.py's pivot-zero hole solution."""
    import numpy as np
    from phi_genesis import mobius

    vertices, edges, _, holes = mobius._sierpinski_full(level)
    boundaries = [mobius._hole_boundary_edges(vertices, edges, h) for h in holes]
    edge_index = {e: i for i, e in enumerate(edges)}
    incidence = np.zeros((len(holes), len(edges)), dtype=np.uint8)
    for h, boundary in enumerate(boundaries):
        for e in boundary:
            incidence[h, edge_index[tuple(sorted(e))]] = 1
    target = np.ones(len(holes), dtype=np.uint8)
    x_pivot = mobius._gf2_solve(incidence, target)
    assert x_pivot is not None
    assert np.array_equal((incidence @ x_pivot) % 2, target)

    # Same local-face representative as the face model, now in mobius edge order.
    x_local = np.array([
        1 if abs(vertices[a][1] - vertices[b][1]) < 1e-10 else 0
        for a, b in edges
    ], dtype=np.uint8)
    local_hole_parity = (incidence @ x_local) % 2
    assert np.all(local_hole_parity == 0), (level, "local face signing should have zero parity on every listed hole")
    local_parity_ones = int(np.count_nonzero(local_hole_parity))
    lambda_pivot = signed_laplacian_smallest(len(vertices), edges, x_pivot)
    lambda_local = signed_laplacian_smallest(len(vertices), edges, x_local)
    assert np.any(x_pivot != x_local), (level, "pivot-zero solution unexpectedly equals local representative")
    hamming_distance = int(np.count_nonzero(x_pivot != x_local))
    return len(vertices), len(edges), len(holes), local_parity_ones, hamming_distance, lambda_pivot, lambda_local


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--compare-repo-max-level", type=int, default=8)
    parser.add_argument("--spectral-max-level", type=int, default=8)
    parser.add_argument("--compare-hole-solver-max-level", type=int, default=6)
    args = parser.parse_args()
    if min(args.max_level, args.compare_repo_max_level, args.spectral_max_level,
           args.compare_hole_solver_max_level) < 0:
        raise SystemExit("levels must be nonnegative")

    print("EXACT_FACE_GAUGE_AUDIT")
    print("level vertices edges faces face_incidence degree triangle_holonomy")
    for m in range(args.max_level + 1):
        vertices, edge_sign, incidence, degree = audit(m)
        print(m, len(vertices), len(edge_sign), 3**m,
              (min(incidence.values()), max(incidence.values())),
              (min(degree.values()), max(degree.values())), -1)

    print("\nREPOSITORY_GRAPH_COMPARISON")
    for m in range(args.compare_repo_max_level + 1):
        nv, ne = compare_repository_graph(m)
        print(m, nv, ne, "exact match")

    print("\nLOWEST_EIGENVALUE_LOCAL_FACE_MODEL L=D-A_sigma, sigma=-s")
    for m in range(1, args.spectral_max_level + 1):
        nv, lam = lowest_face_model_eigenvalue(m)
        print(m, nv, f"{lam:.14f}")

    print("\nPIVOT_ZERO_HOLE_SOLVER_VS_LOCAL_FACE_REPRESENTATIVE")
    print("level vertices edges hole_rows local_x_hole_parity_ones pivot_local_hamming lambda_pivot lambda_local")
    for m in range(1, args.compare_hole_solver_max_level + 1):
        values = compare_hole_solver(m)
        print(values[0], values[1], values[2], values[3], values[4],
              f"{values[5]:.12f}", f"{values[6]:.12f}")


if __name__ == "__main__":
    main()
