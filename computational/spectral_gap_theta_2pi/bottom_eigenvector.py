"""Bottom spectrum of H = D + A_s (local-face theta=2pi model) and
the support of its bottom eigenspace, levels 1..7. Read-only diagnostic."""
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as sla
from audit_triangle_gauge import faces, edge

def build(level):
    idx, seen = {}, {}
    fs = faces(level)
    for f in fs:
        for v in f:
            idx.setdefault(v, len(idx))
    for a, b, c in fs:
        for u, v, s in ((a, b, 1), (a, c, -1), (b, c, -1)):
            e = edge(u, v)
            assert e not in seen, "faces are expected to be edge-disjoint"
            seen[e] = s
    n = len(idx)
    r, c, w = [], [], []
    deg = np.zeros(n)
    for (u, v), s in seen.items():
        i, j = idx[u], idx[v]
        r += [i, j]; c += [j, i]; w += [s, s]
        deg[i] += 1; deg[j] += 1
    H = sp.diags(deg) + sp.csr_matrix((w, (r, c)), shape=(n, n))
    return H, idx

prev = None
for m in range(1, 8):
    H, idx = build(m)
    n = H.shape[0]
    if n <= 1200:
        vals, vecs = np.linalg.eigh(H.toarray())
        k = 12
        vals, vecs = vals[:k], vecs[:, :k]
    else:
        vals, vecs = sla.eigsh(H, k=12, sigma=1.0, which="LM")
        o = np.argsort(vals); vals, vecs = vals[o], vecs[:, o]
    lo = vals[0]
    sel = np.abs(vals - lo) < 1e-9
    P = (vecs[:, sel] ** 2).sum(axis=1)
    inv = {i: v for v, i in idx.items()}
    sup = [inv[i] for i in np.where(P > 1e-10)[0]]
    xs = [p[0] for p in sup]; ys = [p[1] for p in sup]
    d = "" if prev is None else f"  diff_from_prev={lo - prev:.3e}"
    print(f"level {m}: n={n} lambda_min={lo:.15f} multiplicity>={int(sel.sum())}"
          f" support={len(sup)} verts (x {min(xs)}..{max(xs)}, y {min(ys)}..{max(ys)}){d}")
    print("   lowest 6:", " ".join(f"{x:.12f}" for x in vals[:6]))
    prev = lo

try:
    import mpmath
    print("findpoly (15 digits only, NOT a proof):",
          mpmath.findpoly(mpmath.mpf("1.30912892028081"), 4, maxcoeff=2000, tol=1e-12))
except Exception as e:
    print("mpmath not available:", e)
