#!/usr/bin/env python3
"""Bottom eigenvalue of H = D + A_s (local-face theta = 2 pi model) by exact Schur recursion.

All triangle sign products equal +1, so H is gauge-equivalent to the signless Laplacian Q = D + A of
the Sierpinski graph. T_m(lam) is the boundary Schur matrix obtained by eliminating non-corner vertices from Q_m - lam I
while withholding the -lam shift on the three retained outer corners (equivalently, the ordinary
Schur complement plus lam I_3), S3-symmetric with diagonal alpha and off-diagonal beta.
Gluing three copies at three midpoints and eliminating the midpoints gives T_(m+1).
Channels at level m (corner diagonal minus lam): A1: alpha + 2 beta - lam, E: alpha - beta - lam.
Level m = 1..4 agrees with direct diagonalization to 40 digits (see the note).
"""
from mpmath import mp, mpf, matrix, findroot, nstr
mp.dps = 260

def step(al, be, lam):
    P = matrix([[al, be, be], [be, al, be], [be, be, al]])
    K = matrix(6, 6)
    for idx in ((0, 3, 4), (1, 3, 5), (2, 4, 5)):      # corners c0,c1,c2, midpoints m01,m02,m12
        for i in range(3):
            for j in range(3):
                K[idx[i], idx[j]] += P[i, j]
    for k in (3, 4, 5):
        K[k, k] -= lam
    S = K[0:3, 0:3] - K[0:3, 3:6] * mp.inverse(K[3:6, 3:6]) * K[3:6, 0:3]
    return S[0, 0], S[0, 1]

def T(m, lam):
    al, be = mpf(2), mpf(1)
    for _ in range(m):
        al, be = step(al, be, lam)
    return al, be

def chan(m, lam, ch):
    al, be = T(m, lam)
    return al + 2 * be - lam if ch == "A1" else al - be - lam

if __name__ == "__main__":
    tol = mpf(10) ** -240
    x = mpf("1.309071065255606840403693384524824825326")
    A1, E = {}, {}
    for m in range(3, 10):
        A1[m] = x = findroot(lambda t: chan(m, t, "A1"), x, tol=tol, maxsteps=300)
        E[m] = findroot(lambda t: chan(m, t, "E"), x, tol=tol, maxsteps=300)
    print("level  A1 root (bottom eigenvalue, 40 decimals)")
    for m in range(3, 10):
        print(f"{m:>5}  {nstr(A1[m], 42)}")
    print("\nIncrements Delta_m = lam_m - lam_(m-1) and ratio Delta_m / Delta_(m-1)^2")
    D = {m: A1[m] - A1[m - 1] for m in range(4, 10)}
    for m in range(4, 10):
        r = "" if m - 1 not in D else f"   ratio = {nstr(D[m] / D[m - 1] ** 2, 10)}"
        print(f"{m:>5}  {nstr(D[m], 8)}{r}")
    print("\nSplitting s_m = E root - A1 root and ratio s_m / s_(m-1)^2")
    s = {m: E[m] - A1[m] for m in range(4, 8)}
    for m in range(4, 8):
        r = "" if m - 1 not in s else f"   ratio = {nstr(s[m] / s[m - 1] ** 2, 8)}"
        print(f"{m:>5}  {nstr(s[m], 8)}{r}")
    print("\nlambda_9 =", nstr(A1[9], 100))
    print("|lambda_9 - lambda_8| =", nstr(abs(A1[9] - A1[8]), 6))
