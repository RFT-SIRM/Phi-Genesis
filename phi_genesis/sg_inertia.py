"""Exact eigenvalue counting on the Sierpinski-gasket graph Laplacian
WITHOUT an eigensolver (Sylvester's law of inertia).

For a symmetric matrix M, the number of negative pivots of its LU (equivalently
LDL^T) factorization without pivoting equals the number of negative
eigenvalues of M. Applied to M = L - sigma*I this gives N(sigma) = #{eigenvalues < sigma}
exactly, from one sparse factorization, with no eigenvectors and no
dense matrix. Memory stays small because a reverse-Cuthill-McKee ordering keeps the
factor banded (the gasket has bandwidth ~ 2^level).

Measured on one CPU core (see README, Open Problem #2): level 9 (29,526 vertices)
~0.6 s per count and ~250 MB; level 10 (88,575 vertices) a few seconds per count and ~700 MB.

LIMITS (honest):
  * sigma must not be (numerically) an eigenvalue: the factorization is singular there and
    a ValueError is raised.
  * This removes the eigensolver bottleneck. It does NOT supply a window-independent estimator
    of the Weyl exponent; see window_slopes() and README Open Problem #2.
"""
import numpy as np
import scipy.sparse as sp
from scipy.sparse.csgraph import reverse_cuthill_mckee
from scipy.sparse.linalg import splu

from .sg_laplacian import sierpinski_graph

THEORY_EXPONENT = np.log(3) / np.log(5)
LN5 = np.log(5)


def sparse_laplacian(level):
    """Graph Laplacian D - A of SG at `level`, RCM-reordered, CSC. Returns (L, n)."""
    V, E, _ = sierpinski_graph(level)
    n = len(V)
    E = np.array(E)
    r = np.r_[E[:, 0], E[:, 1]]
    c = np.r_[E[:, 1], E[:, 0]]
    A = sp.csr_matrix((np.ones(len(r)), (r, c)), shape=(n, n))
    L = sp.diags(np.asarray(A.sum(1)).ravel()) - A
    p = reverse_cuthill_mckee(L.tocsr(), symmetric_mode=True)
    return L.tocsr()[p][:, p].tocsc(), n


def count_below(L, sigma):
    """Number of eigenvalues of L strictly below sigma (exact, via inertia)."""
    M = (L - sigma * sp.identity(L.shape[0], format="csc")).tocsc()
    try:
        lu = splu(M, permc_spec="NATURAL", diag_pivot_thresh=0.0,
                  options=dict(SymmetricMode=True))
    except RuntimeError as exc:
        raise ValueError(f"sigma={sigma} is (numerically) an eigenvalue") from exc
    d = lu.U.diagonal()
    if np.min(np.abs(d)) < 1e-12:
        raise ValueError(f"sigma={sigma} is (numerically) an eigenvalue")
    return int(np.sum(d < 0))


def counting_function(level, sigmas):
    """N(sigma) for each sigma in `sigmas` at the given SG level."""
    L, _ = sparse_laplacian(level)
    return np.array([count_below(L, s) for s in sigmas], dtype=float)


def window_slopes(sigmas, counts, k, lo_cut, hi_cut, phase_steps=16):
    """Log-log slopes of N(sigma) over windows of width k*ln(5), sliding in steps of
    ln(5)/phase_steps. Returns the array of slopes (one per window position).

    This is deliberately returned as a SPREAD, not a single number: the estimate depends on
    the window width and position (log-periodic oscillation), which is exactly why Open
    Problem #2 remains open."""
    s = np.asarray(sigmas, float)
    N = np.asarray(counts, float)
    ls, lN = np.log(s), np.log(np.where(N > 0, N, np.nan))
    ok = (s >= lo_cut) & (s <= hi_cut) & (N > 0)
    W = k * LN5
    slopes = []
    for st in np.arange(ls[ok].min(), ls[ok].max() - W + 1e-9, LN5 / phase_steps):
        w = (ls >= st - 1e-9) & (ls <= st + W + 1e-9) & ok
        if w.sum() >= 6:
            slopes.append(np.polyfit(ls[w], lN[w], 1)[0])
    return np.array(slopes)
