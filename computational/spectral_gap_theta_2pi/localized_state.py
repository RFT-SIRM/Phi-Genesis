import numpy as np, sympy as sy
from collections import deque
from audit_triangle_gauge import faces, edge

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
    return H, {i: v for v, i in idx.items()}

def comps_of(H, S):
    Sset, left, out = set(S.tolist()), set(S.tolist()), []
    while left:
        s = left.pop(); comp = [s]; q = deque([s])
        while q:
            u = q.popleft()
            for w in np.nonzero(H[u])[0]:
                if w != u and w in left:
                    left.discard(w); comp.append(int(w)); q.append(int(w))
        out.append(sorted(comp))
    return out

first = None
for m in (5, 6):
    H, inv = build(m)
    vals, vecs = np.linalg.eigh(H.astype(float))
    lo = vals[0]
    V = vecs[:, np.abs(vals - lo) < 1e-9]
    resid = np.abs(H @ V - lo * V).max()
    S = np.where((V ** 2).sum(1) > 1e-12)[0]
    cs = comps_of(H, S)
    print(f"level {m}: lambda={lo:.15f} mult={V.shape[1]} support={len(S)} "
          f"components={len(cs)} residual={resid:.1e}")
    for c in cs:
        pts = [inv[i] for i in c]
        xs = [p[0] for p in pts]; ys = [p[1] for p in pts]
        print(f"   comp size={len(c)} box x[{min(xs)},{max(xs)}] y[{min(ys)},{max(ys)}]")
    if m == 5:
        first = (H, cs[0], lo)

H, comp, lo = first
M = sy.Matrix(H[np.ix_(comp, comp)].tolist())
x = sy.symbols("x")
cp = sy.Poly(M.charpoly(x).as_expr(), x)
print("exact charpoly degree", cp.degree(), "of the", len(comp), "-vertex block")
for f, mult in sy.factor_list(cp.as_expr())[1]:
    P = sy.Poly(f, x)
    near = [r for r in P.nroots(n=20) if abs(sy.re(r) - lo) < 1e-8 and abs(sy.im(r)) < 1e-12]
    if near:
        print("FACTOR HOLDING THE EIGENVALUE: degree", P.degree(), "multiplicity", mult)
        print("   polynomial:", P.as_expr())
        print("   root:", near[0])
