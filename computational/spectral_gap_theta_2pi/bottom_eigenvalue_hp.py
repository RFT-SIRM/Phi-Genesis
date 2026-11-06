"""High-precision bottom eigenvalue of H = D + A_s (local-face theta=2pi model), levels 3-8.
Rayleigh quotients in 40-digit arithmetic of double-precision eigenvectors. By the
variational principle each value is an upper bound for the true bottom eigenvalue."""
import numpy as np, scipy.sparse as sp, scipy.sparse.linalg as sla
from mpmath import mp, mpf
mp.dps = 40

def faces(level):
    out = [((0,0),(1,0),(0,1))]
    for depth in range(1, level+1):
        half = 1 << (depth-1)
        old = out
        out = [tuple((x+dx, y+dy) for x, y in f)
               for dx, dy in ((0,0),(half,0),(0,half)) for f in old]
    return out

def build(level):
    idx, seen = {}, {}
    fs = faces(level)
    for f in fs:
        for v in f: idx.setdefault(v, len(idx))
    for a, b, c in fs:
        for u, v, s in ((a,b,1),(a,c,-1),(b,c,-1)):
            e = (u,v) if u < v else (v,u)
            seen[e] = s
    n = len(idx); r=[]; c=[]; w=[]; deg=np.zeros(n, dtype=np.int64)
    for (u,v), s in seen.items():
        i, j = idx[u], idx[v]
        r += [i,j]; c += [j,i]; w += [s,s]; deg[i]+=1; deg[j]+=1
    A = sp.csr_matrix((w,(r,c)), shape=(n,n), dtype=np.int64)
    return (A + sp.diags(deg)).astype(np.int64).tocsr(), n

def rq(H, v):
    Hc = H.tocoo()
    vm = [mpf(float(x)) for x in v]
    nrm = mp.fsum(x*x for x in vm)
    num = mp.fsum(int(h)*vm[i]*vm[j] for i, j, h in zip(Hc.row, Hc.col, Hc.data))
    return num / nrm

lams = {}
for m in range(3, 9):
    H, n = build(m)
    if n <= 1200:
        w, V = np.linalg.eigh(H.toarray().astype(float)); V = V[:, :3]
    else:
        w, V = sla.eigsh(H.astype(float), k=3, sigma=1.3, which="LM", tol=1e-15)
        o = np.argsort(w); V = V[:, o]
    vals = [rq(H, V[:, k]) for k in range(3)]
    lams[m] = min(vals)
    print(f"level {m} n={n}: lambda = {mp.nstr(lams[m], 30)}", flush=True)
    if m-1 in lams:
        d = lams[m-1] - lams[m]
        print(f"    d = {mp.nstr(d, 8)}", flush=True)
        if m-2 in lams:
            dp = lams[m-2] - lams[m-1]
            print(f"    d/d_prev^2 = {mp.nstr(d/dp**2, 8)}", flush=True)
