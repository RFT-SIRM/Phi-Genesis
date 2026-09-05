"""Graph Dirac operator on SG and the eta-invariant claim (REPLICATION TEST).

Constructs D = [[0, B], [B^T, 0]] with B the oriented incidence matrix
(a genuine first-order operator on the graph), adds a vertex potential V,
and measures spectral asymmetry  #(E>0) - #(E<0).

CLAIM TESTED (RFT-String v8.7 report): the boundary potential
    V(i) = v_b * (4 y_i / sqrt(3) - 1)
produces spectral flow eta_bar(0) = -4, hence a = 1/(2*4+1) = 1/9.

RESULT (level 4, v_b = 0.5, and every other potential we tried):
the asymmetry is O(1) and sign-unstable -- for the claimed potential it
is +1, for x(1-x), y(1-y), sin(pi x), or a RANDOM potential it is -1,
for zero potential -2.  The value -4 is NOT observed; the asymmetry is a
finite-size artifact, not a topological invariant.  The claim is REJECTED
by direct numerical replication.
"""
import numpy as np
from scipy.sparse import lil_matrix, csr_matrix
from scipy.sparse.linalg import eigsh
from sg_laplacian import sierpinski_graph


def dirac_spectrum(m, potential=None):
    V, E, _ = sierpinski_graph(m)
    nv, ne = len(V), len(E)
    B = lil_matrix((nv, ne))
    for j, (a, b) in enumerate(E):
        B[a, j] = -1
        B[b, j] = 1
    B = csr_matrix(B)
    D = lil_matrix((nv + ne, nv + ne))
    D[:nv, nv:] = B
    D[nv:, :nv] = B.T
    if potential is not None:
        pot = [float(potential(v)) for v in V]
        for i in range(nv):
            D[i, i] = pot[i]
    vals = eigsh(csr_matrix(D), k=nv + ne - 2, which='SM',
                 return_eigenvectors=False, tol=1e-10)
    return np.sort(vals)


def spectral_asymmetry(m, potential):
    vals = dirac_spectrum(m, potential)
    return int(np.sum(vals > 1e-9) - np.sum(vals < -1e-9))


CLAIMED_POTENTIAL = lambda v: 0.5 * (4 * v[1] / np.sqrt(3) - 1)  # noqa: E731
