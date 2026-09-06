"""Spectral computation on the Sierpinski carpet (membrane construction).

This is an alternative fractal substrate to the Sierpinski gasket (SG):
same idea (build a pre-fractal graph, compute the combinatorial graph
Laplacian, look at its spectrum), different geometry (square holes
instead of triangular ones, spectral dimension ~1.8 instead of ~1.58).

Construction (Barlow-Bass "membrane" graph, standard in the literature):
  - Level m has a 3^m x 3^m grid of unit cells; a cell survives unless
    any base-3 digit pair of its (row, col) index is (1, 1) (the usual
    carpet removal rule).
  - Vertices = lattice points of the (3^m+1) x (3^m+1) grid that touch
    at least one surviving cell.
  - Edges = grid edges between adjacent lattice points, kept whenever at
    least one of the (up to two) cells bordering that edge survives.

This reproduces the vertex counts reported for the carpet elsewhere
(96 / 688 / 5280 vertices at levels 2 / 3 / 4), which is the only
external check available on this construction.

HONEST STATUS: an exploratory search over oscillatory potentials
V(x,y) = scale*sin(freq*(x+y)) on this graph was reported to reach a
"4/4" match against the fermion-mass indices {1, 12, 17, 40} at level 4.
See test_carpet_lookelsewhere.py (nightly suite) for why this is NOT
evidence of a selection rule: a null test shows the four index-hits are
statistically INDEPENDENT of each other (no shared mechanism), and a
Monte-Carlo sweep shows >=3/4 hits by pure chance ~11% of the time and
4/4 ~0.1% of the time per random trial -- consistent with a
look-elsewhere effect given the number of configurations actually
tried, not with a real selection mechanism.
"""
import numpy as np


def cell_survives(i, j, m):
    """Standard Sierpinski carpet removal rule: cell (i, j) in a
    3^m x 3^m grid survives iff no base-3 digit pair of (i, j) is (1, 1)."""
    for _ in range(m):
        if i % 3 == 1 and j % 3 == 1:
            return False
        i //= 3
        j //= 3
    return True


def build_carpet_graph(m):
    """Pre-fractal carpet at level m via the membrane construction.
    Returns (coords, edges) with coords normalized to [0, 1]^2."""
    n_cells = 3 ** m
    survive = np.zeros((n_cells, n_cells), dtype=bool)
    for i in range(n_cells):
        for j in range(n_cells):
            survive[i, j] = cell_survives(i, j, m)

    n_pts = n_cells + 1
    edges = set()

    # horizontal edges: (i,j)-(i+1,j) borders cell row j-1 and row j (col i)
    for i in range(n_cells):
        for j in range(n_pts):
            above = survive[i, j - 1] if j - 1 >= 0 else False
            below = survive[i, j] if j < n_cells else False
            if above or below:
                edges.add(((i, j), (i + 1, j)))

    # vertical edges: (i,j)-(i,j+1) borders cell col i-1 and col i (row j)
    for i in range(n_pts):
        for j in range(n_cells):
            left = survive[i - 1, j] if i - 1 >= 0 else False
            right = survive[i, j] if i < n_cells else False
            if left or right:
                edges.add(((i, j), (i, j + 1)))

    used_pts = sorted(set(p for e in edges for p in e))
    idx = {p: k for k, p in enumerate(used_pts)}
    E = [(idx[a], idx[b]) for a, b in edges]
    coords = np.array([[p[0] / n_cells, p[1] / n_cells] for p in used_pts])
    return coords, E


def carpet_laplacian_spectrum(m, potential=None):
    """Eigenvalues of the combinatorial graph Laplacian at level m,
    sorted. `potential`, if given, is added to the diagonal (per-vertex
    on-site term), same convention as phi_genesis.mass_check's mass
    formula tests."""
    coords, E = build_carpet_graph(m)
    return spectrum_from_graph(coords, E, potential)


def spectrum_from_graph(coords, E, potential=None):
    """Same as carpet_laplacian_spectrum, but takes an already-built
    (coords, E) pair so callers doing many potentials on the same
    level (e.g. Monte-Carlo sweeps) don't rebuild the graph every time."""
    n = len(coords)
    L = np.zeros((n, n))
    deg = np.zeros(n)
    for a, b in E:
        L[a, b] = -1
        L[b, a] = -1
        deg[a] += 1
        deg[b] += 1
    for i in range(n):
        L[i, i] = deg[i]
        if potential is not None:
            L[i, i] += potential[i]
    return np.sort(np.linalg.eigvalsh(L))


def carpet_weyl_check(m):
    """Fit N(lambda) ~ lambda^exponent on the carpet spectrum. Theory:
    d_s/2 = ln(8)/ln(3)/2 -- NOTE this converges much more slowly than
    the gasket's ln(3)/ln(5) (observed ~13.7% error at level 3 vs the
    gasket's ~2.8% at level 8), so treat any carpet spectral-dimension
    claim at low levels with extra caution."""
    theory = np.log(8) / np.log(9)  # d_s/2 for the standard carpet
    spec = carpet_laplacian_spectrum(m)
    nz = spec[spec > 1e-8]
    N = np.arange(1, len(nz) + 1)
    mask = (nz > 1e-4) & (nz < 0.5)
    slope = np.polyfit(np.log(nz[mask]), np.log(N[mask]), 1)[0]
    return slope, theory


def gap_selected_indices(spectrum, k=12, window=60):
    """Indices immediately after the k largest RATIO gaps (lambda[i+1]/
    lambda[i]) within the lowest `window` nonzero eigenvalues.

    This reproduces, index-for-index, the baseline (no-potential)
    results reported for this construction at levels 2 and 3
    ([2,3,4,7,9,12,15,18,20,27,30,37] and
     [2,3,4,7,9,12,15,20,23,27,32,51]), which is the basis for treating
    it as a faithful reconstruction of the method being audited."""
    nz = spectrum[spectrum > 1e-8][:window]
    ratios = nz[1:] / nz[:-1]
    top = np.argsort(ratios)[::-1][:k]
    return sorted((top + 1).tolist())
