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
        return solution


@dataclass
class GenerationFluxProblem:
    level: int
    vertices: list[tuple[float, float]]
    edges: list[tuple[int, int]]
    corners: list[int]
    holes: list[list[int]]
    boundaries: list[list[tuple[int, int]]]
    system: PackedGF2System
    generation_rhs: list[int]
    generation_solutions: list[int]

    def solution(self, generation_mask: int) -> int:
        if generation_mask < 0 or generation_mask >= (1 << self.level):
            raise ValueError(f"generation mask must lie in [0, 2^{self.level})")
        result = 0
        bit = 0
        mask = generation_mask
        while mask:
            if mask & 1:
                result ^= self.generation_solutions[bit]
            mask >>= 1
            bit += 1
        return result


def build_generation_flux_problem(level: int) -> GenerationFluxProblem:
    """Build the signed-cocycle constraint system and generation basis."""
    vertices, edges, corners, holes = sierpinski_graph_with_holes(level)
    edge_index = {edge: i for i, edge in enumerate(edges)}
    context = _boundary_context(vertices, edges, level)
    boundaries = [hole_boundary_edges(vertices, edges, hole, level, context) for hole in holes]
    row_bits = []
    for boundary in boundaries:
        bits = 0
        for edge in boundary:
            bits |= 1 << edge_index[tuple(sorted(edge))]
        row_bits.append(bits)
    system = PackedGF2System(row_bits, len(edges))
    generation_rhs = [0] * level
    for hole_index, hole in enumerate(holes):
        generation_rhs[hole[3] - 1] |= 1 << hole_index
    generation_solutions = [system.solve(rhs) for rhs in generation_rhs]
    return GenerationFluxProblem(
        level, vertices, edges, corners, holes, boundaries, system,
        generation_rhs, generation_solutions,
    )


def signed_laplacian(problem: GenerationFluxProblem, generation_mask: int = 0) -> sp.csr_matrix:
    """Build the exact integer signed Laplacian D - A_s."""
    sign_bits = problem.solution(generation_mask)
    n = len(problem.vertices)
    rows: list[int] = []
    cols: list[int] = []
    values: list[int] = []
    degree = np.zeros(n, dtype=np.int64)
    for edge_index, (a, b) in enumerate(problem.edges):
        sign = -1 if ((sign_bits >> edge_index) & 1) else 1
        rows.extend((a, b))
        cols.extend((b, a))
        values.extend((-sign, -sign))
        degree[a] += 1
        degree[b] += 1
    rows.extend(range(n))
    cols.extend(range(n))
    values.extend(int(x) for x in degree)
    return sp.coo_matrix(
        (np.asarray(values, dtype=np.int64), (rows, cols)),
        shape=(n, n), dtype=np.int64,
    ).tocsr()


def _check_int64_trace_bound(n: int, max_degree: int, power: int):
    row_sum_bound = 2 * max_degree
    trace_bound = n * (row_sum_bound ** power)
    if trace_bound >= INT64_MAX:
        raise OverflowError(
            f"conservative int64 trace bound {trace_bound} exceeds signed int64"
        )


def trace_power_sequential(matrix: sp.csr_matrix, power: int) -> int:
    """Exact sequential sparse-integer trace; useful as a reference check."""
    if power < 1:
        raise ValueError("power must be positive")
    maximum_degree = int(matrix.diagonal().max(initial=0))
    _check_int64_trace_bound(matrix.shape[0], maximum_degree, power)
    product = sp.identity(matrix.shape[0], dtype=np.int64, format="csr")
    for _ in range(power):
        product = (product @ matrix).tocsr()
        product.eliminate_zeros()
    return int(product.diagonal().sum(dtype=np.int64))


def trace_even_power_frobenius(matrix: sp.csr_matrix, power: int) -> int:
    """Exact Tr(L^p)=||L^(p/2)||_F^2 for symmetric integer matrices and even p."""
    if power < 2 or power % 2:
        raise ValueError("power must be a positive even integer")
    if (matrix != matrix.T).nnz:
        raise ValueError("Frobenius trace identity requires a symmetric matrix")
    maximum_degree = int(matrix.diagonal().max(initial=0))
    _check_int64_trace_bound(matrix.shape[0], maximum_degree, power)
    half = power // 2
    product = sp.identity(matrix.shape[0], dtype=np.int64, format="csr")
    for _ in range(half):
        product = (product @ matrix).tocsr()
        product.eliminate_zeros()
    return int(product.multiply(product).sum(dtype=np.int64))


def validate_against_reference(max_level: int = 5, all_generation_masks_at_level: int = 5):
    """Compare optimized boundaries/solver with the original source on small levels."""
    report = []
    for level in range(1, max_level + 1):
        problem = build_generation_flux_problem(level)
        for hole, actual in zip(problem.holes, problem.boundaries):
            reference = _boundary_edges_reference(problem.vertices, problem.edges, hole)
            if actual != reference:
                raise AssertionError((level, hole, actual, reference))

        masks = range(1 << level) if level <= all_generation_masks_at_level else [0, (1 << level) - 1]
        edge_index = {edge: i for i, edge in enumerate(problem.edges)}
        dense_matrix = np.zeros((len(problem.holes), len(problem.edges)), dtype=np.uint8)
        for row, boundary in enumerate(problem.boundaries):
            for edge in boundary:
                dense_matrix[row, edge_index[tuple(sorted(edge))]] = 1
        mask_checks = 0
        for mask in masks:
            rhs = np.zeros(len(problem.holes), dtype=np.uint8)
            for i, hole in enumerate(problem.holes):
                rhs[i] = (mask >> (hole[3] - 1)) & 1
            reference, _, _ = _gf2_solve_reference(dense_matrix, rhs)
            if reference is None:
                raise AssertionError(f"reference system inconsistent at level {level}, mask {mask}")
            actual_bits = problem.solution(mask)
            actual = np.fromiter(
                ((actual_bits >> j) & 1 for j in range(len(problem.edges))),
                dtype=np.uint8, count=len(problem.edges),
            )
            if not np.array_equal(reference, actual):
                raise AssertionError(f"GF(2) mismatch at level {level}, mask {mask}")
            mask_checks += 1
        report.append({
            "level": level,
            "vertices": len(problem.vertices),
            "edges": len(problem.edges),
            "holes": len(problem.holes),
            "boundary_rank": problem.system.rank,
            "reference_masks_checked": mask_checks,
        })
    return report


def q_transition(a: int, b: int, c: int, d: int) -> int:
    """Finite-data H10 transition polynomial Q for Boolean generation bits."""
    if any(x not in (0, 1) for x in (a, b, c, d)):
        raise ValueError("a, b, c, d must be Boolean")
    return (
        127182024
        + 89195520 * a + 73945440 * b - 145153920 * a * b
        + 55360 * c - 150880 * a * c + 40320 * b * c - 39680 * a * b * c
        + d * (
            115347760 - 110022480 * a + 10024960 * b
            - 20854720 * a * b + 320 * c - 640 * a * c
        )
    )


def compute_full_flux_h10(max_level: int = 10) -> list[dict[str, int]]:
    """Compute untwisted/full-flux tenth traces and residuals through max_level."""
    if max_level < 1:
        raise ValueError("max_level must be at least 1")
    records = []
    previous_defect = None
    for level in range(1, max_level + 1):
        problem = build_generation_flux_problem(level)
        untwisted = trace_even_power_frobenius(signed_laplacian(problem, 0), 10)
        full_mask = (1 << level) - 1
        full_flux = trace_even_power_frobenius(signed_laplacian(problem, full_mask), 10)
        defect = full_flux - untwisted
        row = {
            "level": level,
            "vertices": len(problem.vertices),
            "edges": len(problem.edges),
            "holes": len(problem.holes),
            "boundary_rank": problem.system.rank,
            "trace_untwisted": untwisted,
            "trace_full_flux": full_flux,
            "D10": defect,
        }
        if previous_defect is not None:
            row["residual"] = defect - 3 * previous_defect
        records.append(row)
        previous_defect = defect
    return records


def compute_generation_twist_traces(level: int) -> list[int]:
    """Compute Tr(L^10) for all 2**level generation-twist masks."""
    problem = build_generation_flux_problem(level)
    values = []
    for mask in range(1 << level):
        values.append(trace_even_power_frobenius(signed_laplacian(problem, mask), 10))
    return values


if __name__ == "__main__":
    import argparse
    import csv
    import json
    from pathlib import Path

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-level", type=int, default=10)
    parser.add_argument("--output", type=Path, default=Path("h10_full_flux_levels.csv"))
    parser.add_argument("--validate-reference", action="store_true")
    parser.add_argument("--generation-level", type=int, default=None,
                        help="also compute all generation-twist masks at this level")
    parser.add_argument("--generation-output", type=Path, default=None,
                        help="optional CSV path for the generation-twist sweep")
    args = parser.parse_args()
    if args.validate_reference:
        print(json.dumps(validate_against_reference(), indent=2))
    rows = compute_full_flux_h10(args.max_level)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", newline="") as stream:
        writer = csv.DictWriter(
            stream,
            fieldnames=[
                "level", "vertices", "edges", "holes", "boundary_rank",
                "trace_untwisted", "trace_full_flux", "D10", "residual",
            ],
        )
        writer.writeheader()
        writer.writerows(rows)
    print(f"wrote {args.output}")
    if args.generation_level is not None:
        traces = compute_generation_twist_traces(args.generation_level)
        if args.generation_output is not None:
            args.generation_output.parent.mkdir(parents=True, exist_ok=True)
            with args.generation_output.open("w", newline="") as stream:
                writer = csv.DictWriter(
                    stream, fieldnames=["level", "generation_mask", "twisted_generations", "trace10"]
                )
                writer.writeheader()
                for mask, trace in enumerate(traces):
                    generations = [
                        str(j + 1) for j in range(args.generation_level) if (mask >> j) & 1
                    ]
                    writer.writerow({
                        "level": args.generation_level,
                        "generation_mask": mask,
                        "twisted_generations": ",".join(generations),
                        "trace10": trace,
                    })
            print(f"wrote {args.generation_output}")
        print(json.dumps({
            "level": args.generation_level,
            "configurations": len(traces),
            "distinct_trace_values": len(set(traces)),
            "all_distinct": len(set(traces)) == len(traces),
        }, indent=2))
