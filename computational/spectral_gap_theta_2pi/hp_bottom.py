import numpy as np
from mpmath import mp, mpf, matrix
from audit_triangle_gauge import faces, edge
mp.dps = 50

def build(level):
    idx, seen = {}, {}
    fs = faces(level)
    for f in fs:
        for v in f:
            idx.setdefault(v, len(idx))
    for a, b, c in fs:
        for u, v, s in ((a, b, 1), (a, c, -1), (b, c, -1)):
            seen[edge(u, v)] = s
    n = len(idx)
    H = np.zeros((n, n), dtype=np.int64)
    for (u, v), s in seen.items():
        i, j = idx[u], idx[v]
        H[i, j] = H[j, i] = s
        H[i, i] += 1; H[j, j] += 1
    return H

lam = {}
for m in (3, 4, 5):
    H = build(m); n = H.shape[0]
    w, V = np.linalg.eigh(H.astype(float))
    mu = mpf(float(w[0]))
    A = matrix(n, n)
    for i in range(n):
        for j in np.nonzero(H[i])[0]:
            A[i, int(j)] = mpf(int(H[i, j]))
        A[i, i] -= mu
    LU, p = mp.LU_decomp(A)
    v = matrix([mpf(float(x)) for x in V[:, 0]])
    for _ in range(3):
        y = mp.L_solve(LU, v, p)
        v = mp.U_solve(LU, y)
        v = v / mp.norm(v)
    Hm = matrix(n, n)
    for i in range(n):
        for j in np.nonzero(H[i])[0]:
            Hm[i, int(j)] = mpf(int(H[i, j]))
    lam[m] = (v.T * (Hm * v))[0]
    print(f"level {m}: lambda = {mp.nstr(lam[m], 40)}", flush=True)
    if m - 1 in lam:
        d = lam[m - 1] - lam[m]
        print(f"   d = {mp.nstr(d, 12)}", flush=True)
        if m - 2 in lam:
            dp = lam[m - 2] - lam[m - 1]
            print(f"   d / d_prev^2 = {mp.nstr(d / dp**2, 12)}", flush=True)
