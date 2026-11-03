"""Exact finite-level H10 experiments for the signed Sierpinski-gasket Laplacian.

The conventions match :mod:`phi_genesis.mobius`:
- the recursive Sierpinski graph and its listed holes;
- one GF(2) parity equation for each listed hole boundary;
- non-pivot edge variables set to zero;
- the signed Laplacian L = D - A_s.

The packed GF(2) implementation and triangular-lattice boundary walk are
computational optimisations.  ``validate_against_reference`` compares them
with the original dense solver and geometric boundary scan on small levels.
All trace routines use integer sparse arithmetic and check a conservative
int64 bound before multiplication.  These are finite computational
certificates, not an all-level theorem.
"""
from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Iterable

import numpy as np
import scipy.sparse as sp

SQRT3_HALF = math.sqrt(3.0) / 2.0
INT64_MAX = np.iinfo(np.int64).max


def sierpinski_graph_with_holes(level: int):
    """Return ``(vertices, edges, outer_corners, holes)`` as in ``mobius.py``."""
    if level < 0:
        raise ValueError("level must be non-negative")
    if level == 0:
        return (
            [(0.0, 0.0), (1.0, 0.0), (0.5, SQRT3_HALF)],
            [(0, 1), (1, 2), (0, 2)],
            [0, 1, 2],
            [],
        )

    vertices0, edges0, corners0, holes0 = sierpinski_graph_with_holes(level - 1)
    targets = [np.array([0.0, 0.0]), np.array([1.0, 0.0]), np.array([0.5, SQRT3_HALF])]
    vertices: list[tuple[float, float]] = []
    edges: list[tuple[int, int]] = []
    for child in range(3):
        offset = targets[child]
        old_corner = np.array(vertices0[corners0[child]])
        base = len(vertices)
        for vertex in vertices0:
            vertices.append(tuple(offset + 0.5 * (np.array(vertex) - old_corner)))
        for a, b in edges0:
            edges.append((base + a, base + b))

    coord_to_id: dict[tuple[float, float], int] = {}
    remap: dict[int, int] = {}
    merged_vertices: list[tuple[float, float]] = []
    for old_id, vertex in enumerate(vertices):
        key = (round(vertex[0], 12), round(vertex[1], 12))
        if key not in coord_to_id:
            coord_to_id[key] = len(merged_vertices)
            merged_vertices.append(vertex)
        remap[old_id] = coord_to_id[key]

    merged_edges = sorted({tuple(sorted((remap[a], remap[b]))) for a, b in edges})
    corners = [remap[child * len(vertices0) + corners0[child]] for child in range(3)]
    holes = [
        [
            remap[child * len(vertices0) + hole[0]],
            remap[child * len(vertices0) + hole[1]],
            remap[child * len(vertices0) + hole[2]],
            hole[3],
        ]
        for child in range(3)
        for hole in holes0
    ]
    holes.append([corners[0], corners[1], corners[2], level])
    return merged_vertices, merged_edges, corners, holes


def _boundary_context(vertices, edges, level: int):
    scale = 1 << level
    coord_to_id = {}
    for index, (x, y) in enumerate(vertices):
        key = (
            int(round((x - y / math.sqrt(3.0)) * scale)),
            int(round((y / SQRT3_HALF) * scale)),
        )
        coord_to_id[key] = index
    return coord_to_id, set(edges), scale


def hole_boundary_edges(vertices, edges, hole, level: int, context=None):
    """Fast exact edge-list extraction on the triangular lattice."""
    coord_to_id, edge_set, scale = context or _boundary_context(vertices, edges, level)
    result = set()
    for start_id, end_id in ((hole[0], hole[1]), (hole[1], hole[2]), (hole[0], hole[2])):
        x0, y0 = vertices[start_id]
        x1, y1 = vertices[end_id]
        p = (
            int(round((x0 - y0 / math.sqrt(3.0)) * scale)),
            int(round(y0 / SQRT3_HALF * scale)),
        )
        q = (
            int(round((x1 - y1 / math.sqrt(3.0)) * scale)),
            int(round(y1 / SQRT3_HALF * scale)),
        )
        dx, dy = q[0] - p[0], q[1] - p[1]
        steps = math.gcd(abs(dx), abs(dy))
        if steps == 0:
            raise ValueError("hole boundary has a degenerate side")
        points = []
        for step in range(steps + 1):
            key = (p[0] + (dx // steps) * step, p[1] + (dy // steps) * step)
            if key in coord_to_id:
                points.append(coord_to_id[key])
        for a, b in zip(points[:-1], points[1:]):
            edge = tuple(sorted((a, b)))
            if edge in edge_set:
                result.add(edge)
    return sorted(result)


def _boundary_edges_reference(vertices, edges, hole):
    """Literal geometric scan from ``mobius.py``; used only for validation."""
    a, b, c = hole[:3]
    edge_set = set(edges)
    boundary = set()
    for p, q in ((a, b), (b, c), (a, c)):
        P, Q = np.array(vertices[p]), np.array(vertices[q])
        d = Q - P
        on_segment = [
            i for i, vertex in enumerate(vertices)
            if abs(d[0] * (vertex[1] - P[1]) - d[1] * (vertex[0] - P[0])) < 1e-9
            and min(P[0], Q[0]) - 1e-9 <= vertex[0] <= max(P[0], Q[0]) + 1e-9
            and min(P[1], Q[1]) - 1e-9 <= vertex[1] <= max(P[1], Q[1]) + 1e-9
        ]
        on_segment.sort(key=lambda i: float(np.dot(np.array(vertices[i]) - P, d)))
        for u, w in zip(on_segment[:-1], on_segment[1:]):
            edge = tuple(sorted((u, w)))
            if edge in edge_set:
                boundary.add(edge)
    return sorted(boundary)


def _gf2_solve_reference(matrix: np.ndarray, rhs: np.ndarray):
    """Dense RREF solver copied from the project reference implementation."""
    matrix = matrix.copy().astype(np.uint8) % 2
    rhs = rhs.copy().astype(np.uint8) % 2
    row_count, col_count = matrix.shape
    augmented = np.concatenate([matrix, rhs[:, None]], axis=1)
    row = 0
    pivots = []
    for col in range(col_count):
        candidates = np.where(augmented[row:, col])[0]
        if len(candidates) == 0:
            continue
        pivot_row = row + int(candidates[0])
        augmented[[row, pivot_row]] = augmented[[pivot_row, row]]
        for other in np.where(augmented[:, col])[0]:
            if other != row:
                augmented[other] ^= augmented[row]
        pivots.append(col)
        row += 1
        if row == row_count:
            break
    for other in range(row, row_count):
        if augmented[other, col_count]:
            return None, pivots, row
    solution = np.zeros(col_count, dtype=np.uint8)
    for i, col in enumerate(pivots):
        solution[col] = augmented[i, col_count]
    return solution, pivots, row


@dataclass
class PackedGF2System:
    """GF(2) linear system retaining row-combination witnesses for each pivot."""

    rows: list[int]
    ncols: int

    def __post_init__(self):
        basis: dict[int, tuple[int, int]] = {}
        dependencies: list[int] = []
        for row_index, original in enumerate(self.rows):
            bits = original
            combination = 1 << row_index
            while bits:
                pivot = (bits & -bits).bit_length() - 1
                if pivot in basis:
                    basis_row, basis_combination = basis[pivot]
                    bits ^= basis_row
                    combination ^= basis_combination
                else:
                    basis[pivot] = (bits, combination)
                    break
            if bits == 0:
                dependencies.append(combination)
        self._basis = basis
        self._dependencies = dependencies

    @property
    def rank(self) -> int:
        return len(self._basis)

    def solve(self, rhs: int) -> int:
        for dependency in self._dependencies:
            if (dependency & rhs).bit_count() & 1:
                raise ValueError("inconsistent GF(2) system")
        solution = 0
        for pivot in sorted(self._basis, reverse=True):
            row, combination = self._basis[pivot]
            value = ((combination & rhs).bit_count() & 1) ^ ((row & solution).bit_count() & 1)
            if value:
                solution |= 1 << pivot
        return solution‚