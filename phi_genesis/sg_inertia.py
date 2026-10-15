"""Eigenvalue counting on the Sierpinski-gasket graph Laplacian with a sparse LU
factorization (Sylvester's law of inertia), without an eigensolver.

Mathematics (exact arithmetic). For a real symmetric matrix M whose leading principal minors
are all nonzero, the LU factorization without pivoting exists and the number of negative
pivots (diagonal entries of U) equals the number of negative eigenvalues of M (Sylvester's
law of inertia, via M = L D L^T). With M = L - sigma*I this is N(sigma) = #{eigenvalues < sigma}.

Implementation (floating point). scipy.sparse.linalg.splu (SuperLU) is run on a reverse
Cuthill-McKee ordering with diag_pivot_thresh=0 (diagonal pivots preferred) and natural column
order, in double precision. The computed pivots are those of a nearby matrix M + E. The count
equals the true N(sigma) when E does not change the inertia, which is guaranteed (Weyl's
inequality) if ||E||_2 < min_i |lambda_i - sigma|. No bound on ||E|| is computed here, and
without row pivoting its growth is not bounded a priori. The returned integer is therefore a
numerical result whose reliability depends on how far sigma is from the spectrum; it is not an
exact certificate. The only guard is a ValueError when the factorization fails or the smallest
|pivot| is below 1e-12.

Measured behaviour (levels 5-7; reference: dense numpy.linalg.eigvalsh; sigma = lambda +- delta
for every distinct eigenvalue lambda; 992 sigma per delta):
  * delta from 1e-1 to 1e-8: the count was correct in every one of the 7936 tests.
  * delta = 1e-9 and 1e-10: 18 wrong counts were returned WITHOUT a ValueError (of 1984 tests),
    all next to the eigenvalue 3 (multiplicity 39, 120, 363 at levels 5, 6, 7) or the simple
    eigenvalue 4; the largest error was 65 (for example 1041 instead of 1095 at level 7,
    sigma = 3 + 1e-9). The smallest pivot in those cases was between 3.5e-11 and 1.7e-8, so the
    pivot guard is NOT a reliable detector of an unreliable count (a stricter threshold of
    1e-8 reduced but did not remove such cases: level 5, sigma = 3 + 1e-9, smallest pivot
    1.7e-8, count 121 instead of 123).
  * the sigma grids used for Open Problem #2 at levels 8 and 9 (and phi of each sigma) have a
    smallest pivot of at least 4e-5; level 10 was not checked.
Keep sigma well away from eigenvalues (the tests use at least 1e-6) or confirm a count by
repeating it at slightly shifted sigma.

LIMITS:
  * sigma must be separated from the spectrum; near an eigenvalue the result can be wrong
    without an error.
  * This removes the eigensolver bottleneck. It does NOT supply a window-independent estimator
    of the Weyl exponent; see window_slopes() and README Open Problem #2.

Cost, measured on one CPU core (see README, Open Problem #2): level 9 (29,526 vertices)
~0.6 s per count and ~250 MB; level 10 (88,575 vertices) a few seconds per count and ~700 MB.
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
    """Numerical inertia count of the eigenvalues of L strictly below sigma.

    Mathematically N(sigma) = #{lambda < sigma} (Sylvester's law of inertia); computed in floating
    point, so reliable only for sigma separated from the spectrum (see the module docstring for the
    measured limits). Raises ValueError if the factorization fails or the smallest |pivot| is below
    1e-12; that guard does not catch every wrong count near an eigenvalue.
    """
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
