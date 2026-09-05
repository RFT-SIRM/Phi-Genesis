"""Real spectral computation on the Sierpinski gasket.

Builds the pre-fractal graph at level m, computes the combinatorial graph
Laplacian spectrum, and verifies the two classic results:
  1. Spectral decimation: eigenvalues scale by factor ~5 per level
     (exact decimation polynomial: lambda_m = lambda_{m+1} * (5 - lambda_{m+1}))
  2. Weyl law: N(lambda) ~ lambda^{d_s/2}, d_s/2 = ln(3)/ln(5) ~ 0.6826,
     with log-periodic oscillations of period ln 5.
"""
import numpy as np
from scipy.sparse import lil_matrix, csr_matrix
from scipy.sparse.linalg import eigsh


def sierpinski_graph(m):
    """Pre-fractal SG at level m. Returns (vertices, edges, corner_indices)."""
    if m == 0:
        V = [(0.0, 0.0), (1.0, 0.0), (0.5, np.sqrt(3) / 2)]
        return V, [(0, 1), (1, 2), (0, 2)], [0, 1, 2]
    V0, E0, C0 = sierpinski_graph(m - 1)
    targets = [np.array([0.0, 0.0]), np.array([1.0, 0.0]),
               np.array([0.5, np.sqrt(3) / 2])]
    V, E = [], []
    for c in range(3):
        off = targets[c]
        corner_c = np.array(V0[C0[c]])
        base = len(V)
        for v in V0:
            V.append(tuple(off + 0.5 * (np.array(v) - corner_c)))
        for a, b in E0:
            E.append((base + a, base + b))
    coord2id, remap, newV = {}, {}, []
    for i, v in enumerate(V):
        key = (round(v[0], 12), round(v[1], 12))
        if key not in coord2id:
            coord2id[key] = len(newV)
            newV.append(v)
        remap[i] = coord2id[key]
    newE = sorted(set(tuple(sorted((remap[a], remap[b]))) for a, b in E))
    newC = [remap[c * len(V0) + C0[c]] for c in range(3)]
    return newV, newE, newC


def graph_laplacian_spectrum(m):
    """Eigenvalues of the combinatorial graph Laplacian at level m, sorted."""
    V, E, _ = sierpinski_graph(m)
    n = len(V)
    L = lil_matrix((n, n))
    deg = np.zeros(n)
    for a, b in E:
        L[a, b] = -1
        L[b, a] = -1
        deg[a] += 1
        deg[b] += 1
    for i in range(n):
        L[i, i] = deg[i]
    vals = eigsh(csr_matrix(L), k=n - 2, which='SM', return_eigenvectors=False)
    return np.sort(vals)


def spectral_dimension_check(level=6):
    """Fit N(lambda) ~ lambda^exponent. Returns (fitted, theory=ln3/ln5)."""
    spec = graph_laplacian_spectrum(level)
    nz = spec[spec > 1e-8]
    N = np.arange(1, len(nz) + 1)
    mask = (nz > 1e-4) & (nz < 0.5)
    slope = np.polyfit(np.log(nz[mask]), np.log(N[mask]), 1)[0]
    return slope, np.log(3) / np.log(5)


def decimation_ratio(level=6):
    """Ratio of matching eigenvalues between two consecutive levels.

    Should approach 5 for small eigenvalues (larger index = larger lambda
    shows the -lambda^2 correction of the decimation polynomial).
    """
    lo = graph_laplacian_spectrum(level - 1)
    hi = graph_laplacian_spectrum(level)
    lo = lo[lo > 1e-8]
    hi = hi[hi > 1e-8]
    k = min(len(lo), len(hi))
    return lo[:k] / hi[:k]
