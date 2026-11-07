"""D3 representation audit for the first positive SG Laplacian eigenvalues.

This is an exploratory diagnostic for Open Problem #1, not a preregistered
mass-index selection rule.  It uses the repository's corner-degree-2
combinatorial graph Laplacian and numbers eigenvalues after removing the
constant zero mode, matching PREREGISTRATION.md.

The low eigenspaces are computed with a dense symmetric subset eigensolver.
This is deliberate: iterative sparse eigensolvers may return only part of a
highly degenerate eigenspace, which corrupts character traces.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import permutations
from math import sqrt
from typing import Iterable

import numpy as np
from scipy.linalg import eigh

from .sg_laplacian import sierpinski_graph


_D3_ORDERS = tuple(permutations(range(3)))
_D3_PARITIES = np.asarray(
    [
        -1 if sum(order[i] > order[j] for i in range(3) for j in range(i + 1, 3)) % 2 else 1
        for order in _D3_ORDERS
    ],
    dtype=float,
)


@dataclass(frozen=True)
class SpectralCluster:
    """One numerically clustered eigenspace, ranked in the positive spectrum."""

    start: int
    end: int
    multiplicity: int
    a1: int
    a2: int
    e_multiplicity: int
    eigenvalue: float


@dataclass(frozen=True)
class SymmetryAudit:
    level: int
    vertex_count: int
    positive_window: int
    clusters: tuple[SpectralCluster, ...]

    def cluster_containing(self, positive_rank: int) -> SpectralCluster:
        """Return the complete computed cluster containing a 1-based positive rank."""
        if positive_rank < 1 or positive_rank > self.positive_window:
            raise ValueError("positive_rank must lie inside the audited positive window")
        for cluster in self.clusters:
            if cluster.start <= positive_rank <= cluster.end:
                return cluster
        raise RuntimeError(f"no computed cluster contains positive rank {positive_rank}")

    def signature(self) -> tuple[tuple[int, int, int, int, int, int], ...]:
        """Cluster endpoints and D3 multiplicities, independent of eigenvalue scale."""
        return tuple(
            (c.start, c.end, c.multiplicity, c.a1, c.a2, c.e_multiplicity)
            for c in self.clusters
        )

    def simple_a1_ranks(self) -> tuple[int, ...]:
        """Starts of multiplicity-one trivial-irrep eigenspaces in the window."""
        return tuple(c.start for c in self.clusters if c.multiplicity == 1 and c.a1 == 1)

    def to_dict(self) -> dict:
        return {
            "level": self.level,
            "vertex_count": self.vertex_count,
            "positive_window": self.positive_window,
            "clusters": [asdict(cluster) for cluster in self.clusters],
            "simple_a1_ranks": list(self.simple_a1_ranks()),
        }


def _barycentric_key(x: float, y: float, level: int) -> tuple[int, int, int]:
    """Recover integer barycentric coordinates (p,q,r), p+q+r=2**level."""
    scale = 1 << level
    r = int(round(2.0 * y * scale / sqrt(3.0)))
    q = int(round(x * scale - r / 2.0))
    p = scale - q - r
    key = (p, q, r)
    if min(key) < 0 or sum(key) != scale:
        raise ValueError(f"vertex ({x}, {y}) is not on the level-{level} triangle lattice")
    return key


def d3_vertex_permutations(
    vertices: Iterable[tuple[float, float]],
    edges: Iterable[tuple[int, int]],
    level: int,
) -> tuple[np.ndarray, ...]:
    """Construct all six D3 actions and verify that each is a graph automorphism.

    The action permutes the three integer barycentric coordinates.  This avoids
    floating-point trignometric rotations/reflections when building the group.
    """
    vertices = tuple(vertices)
    edges = tuple(tuple(sorted((int(a), int(b))))) for a, b in edges)
    index_of: dict[tuple[int, int, int], int] = {}
    keys: list[tuple[int, int, int]] = []
    for index, (x, y) in enumerate(vertices):
        key = _barycentric_key(float(x), float(y), level)
        if key in index_of:
            raise ValueError(f"duplicate barycentric vertex key: {key}")
        index_of[key] = index
        keys.append(key)

    edge_set = set(edges)
    if len(edge_set) != len(edges):
        raise ValueError("graph contains duplicate undirected edges")

    actions: list[np.ndarray] = []
    for order in _D3_ORDERS:
        action = np.empty(len(vertices), dtype=np.int64)
        for source, key in enumerate(keys):
            target_key = tuple(key[j] for j in order)
            try:
                action[source] = index_of[target_key]
            except KeyError as exc:
                raise ValueError(f"D3 action leaves the level-{level} vertex set: {target_key}") from exc
        if len(np.unique(action)) != len(vertices):
            raise ValueError("constructed D3 action is not a vertex permutation")
        mapped_edges = {
            tuple(sorted((int(action[a]), int(action[b])))) for a, b in edges
        }
        if mapped_edges != edge_set:
            raise ValueError(f"a barycentric permutation is not a graph automorphism at level {level}")
        actions.append(action)
    return tuple(actions)


def _dense_laplacian(vertex_count: int, edges: Iterable[tuple[int, int]]) -> np.ndarray:
    """Build the unweighted combinatorial Laplacian from the graph edge list."""
    edge_array = np.asarray(tuple(edges), dtype=np.int64)
    laplacian = np.zeros((vertex_count, vertex_count), dtype=np.float64)
    degree = np.zeros(vertex_count, dtype=np.float64)
    laplacian[edge_array[:, 0], edge_array[:, 1]] = -1.0
    laplacian[edge_array[:, 1], edge_array[:, 0]] = -1.0
    np.add.at(degree, edge_array[:, 0], 1.0)
    np.add.at(degree, edge_array[:, 1], 1.0)
    laplacian[np.arange(vertex_count), np.arange(vertex_count)] = degree
    return laplacian


def _irrep_multiplicities(
    eigenspace_basis: np.ndarray,
    actions: tuple[np.ndarray, ...],
) -> tuple[int, int, int]:
    """Recover A1, A2 and E multiplicities from D3 character traces.

    For the 1-dimensional irreps A1 and A2, multiplicities are character inner
    products.  The remaining dimension is twice the multiplicity of the
    2-dimensional irrep E.
    """
    traces = np.asarray(
        [np.einsum("ij,ij->", eigenspace_basis, eigenspace_basis[action, :]) for action in actions],
        dtype=np.float64,
    )
    raw_a1 = float(traces.sum() / 6.0)
    raw_a2 = float(np.dot(_D3_PARITIES, traces) / 6.0)
    raw_e = float((eigenspace_basis.shape[1] - raw_a1 - raw_a2) / 2.0)
    rounded = tuple(int(round(value)) for value in (raw_a1, raw_a2, raw_e))
    if any(abs(value - integer) > 5e-5 for value, integer in zip((raw_a1, raw_a2, raw_e), rounded)):
        raise ArithmeticError(
            "D3 character multiplicities are not numerically integral; "
            "check cluster tolerance and eigenspace completeness"
        )
    a1, a2, e_mult = rounded
    multiplicity = eigenspace_basis.shape[1]
    if min(rounded) < 0 or a1 + a2 + 2 * e_mult != multiplicity:
        raise ArithmeticError("D3 irrep dimensions do not reconstruct eigenspace multiplicity")
    return a1, a2, e_mult


def symmetry_probe(
    level: int,
    positive_window: int = 60,
    padding: int = 18,
    cluster_tolerance: float = 1e-8,
) -> SymmetryAudit:
    """Audit D3 content of the first ``positive_window`` positive eigenvalue ranks.

    The constant zero mode is removed before assigning positive-spectrum ranks.
    ``padding`` extra eigenpairs ensure that a cluster crossing the requested
    window is complete.  A cluster that reaches the eigensolver's truncation
    boundary is rejected rather than silently classified as incomplete.
    """
    if level < 1:
        raise ValueError("level must be at least 1")
    if positive_window < 1 or padding < 2:
        raise ValueError("positive_window must be positive and padding at least two")
    if cluster_tolerance <= 0:
        raise ValueError("cluster_tolerance must be positive")

    vertices, edges, _ = sierpinski_graph(level)
    actions = d3_vertex_permutations(vertices, edges, level)
    laplacian = _dense_laplacian(len(vertices), edges)

    # Full-spectrum position 0 is the constant zero mode, so positive rank n
    # corresponds to full-spectrum position n.
    last_full_index = positive_window + padding
    eigenvalues, eigenvectors = eigh(
        laplacian,
        subset_by_index=(0, last_full_index),
        driver="evr",
        check_finite=False,
    )
    if abs(float(eigenvalues[0])) > 1e-8:
        raise ArithmeticError("the first eigenvalue is not the expected constant zero mode")

    clusters: list[SpectralCluster] = []
    start = 1
    while start <= positive_window:
        end_exclusive = start + 1
        while (
            end_exclusive < len(eigenvalues)
            and abs(float(eigenvalues[end_exclusive] - eigenvalues[start])) < cluster_tolerance
        ):
            end_exclusive += 1
        if end_exclusive == len(eigenvalues):
            raise ArithmeticError(
                "spectral padding ended inside a numerically degenerate cluster; increase padding"
            )
        basis = eigenvectors[:, start:end_exclusive]
        a1, a2, e_mult = _irrep_multiplicities(basis, actions)
        clusters.append(
            SpectralCluster(
                start=start,
                end=end_exclusive - 1,
                multiplicity=end_exclusive - start,
                a1=a1,
                a2=a2,
                e_multiplicity=e_mult,
                eigenvalue=float(eigenvalues[start]),
            )
        )
        start = end_exclusive

    return SymmetryAudit(
        level=level,
        vertex_count=len(vertices),
        positive_window=positive_window,
        clusters=tuple(clusters),
    )


def main() -> None:
    audits = {level: symmetry_probe(level) for level in (5, 6, 7)}
    reference = audits[5].signature()
    print("D3 graph automorphisms: verified at levels 5, 6, 7")
    print("positive-spectrum cluster signature 5 == 6 == 7:", all(a.signature() == reference for a in audits.values()))
    print("target | cluster | multiplicity | A1 | A2 | E multiplicity | eigenvalue")
    for rank in (1, 12, 17, 40):
        row = audits[7].cluster_containing(rank)
        print(
            f"{rank:>6} | [{row.start},{row.end}] | {row.multiplicity:>12} | "
            f"{row.a1:>2} | {row.a2:>2} | {row.e_multiplicity:>14} | {row.eigenvalue:.12g}"
        )
    print("simple A1 ranks in positive window:", list(audits[7].simple_a1_ranks()))


if __name__ == "__main__":
    main()
