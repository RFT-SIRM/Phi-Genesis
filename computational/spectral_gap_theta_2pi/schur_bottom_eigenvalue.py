#!/usr/bin/env python3
"""Bottom eigenvalue of H = D + A_s (local-face theta = 2 pi model) by exact Schur recursion.

All triangle sign products equal +1, so H is gauge-equivalent to the signless Laplacian Q = D + A of
the Sierpinski graph. T_m(lam) is the boundary Schur matrix obtained by eliminating non-corner vertices
from Q_m - lam I while withholding the -lam shift on the three retained outer corners (equivalently,
the ordinary Schur complement plus lam I_3). It is S3-symmetric, with diagonal alpha and
off-diagonal beta. Thus the final boundary equations are alpha + 2 beta - lam = 0 (A1) and
alpha - beta - lam = 0 (E).

The default 260-dps run computes A1 roots through level 9 and E roots only through level 7.
The level-9 E/A1 splitting is about 4.7e-291, below this script's working precision, so it is
intentionally not computed or displayed here.
"""
from mpmath import mp, mpf, matrix, findroot, nstr


def step(al, be, lam):
    P = matrix([[al, be, be], [be, al, be], [be, be, al]])
    K = matrix(6, 6)
    for idx in ((0, 3, 4), (1, 3, 5), (2, 4, 5)):  # corners and shared midpoints
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


def compute_roots(a1_max_level=9, e_max_level=7, dps=260):
    """Compute A1 and E boundary roots at a precision that resolves their splittings."""
    if a1_max_level < 3 or e_max_level < 3 or e_max_level > a1_max_level:
        raise ValueError("require 3 <= e_max_level <= a1_max_level")
    with mp.workdps(dps):
        tol = mpf(10) ** (-dps + 20)
        x = mpf("1.309071065255606840403693384524824825326")
        A1 = {}
        for m in range(3, a1_max_level + 1):
            A1[m] = x = findroot(
                lambda t: chan(m, t, "A1"), x, tol=tol, maxsteps=300
            )

        E = {}
        for m in range(3, e_max_level + 1):
            # Seed from the A1 root at the same level. The E/A1 gap is then resolved
            # only while it remains comfortably above the requested precision floor.
            E[m] = findroot(
                lambda t: chan(m, t, "E"), A1[m], tol=tol, maxsteps=300
            )
        return A1, E


def main():
    A1, E = compute_roots(a1_max_level=9, e_max_level=7, dps=260)
    print("level  A1 root (bottom eigenvalue, 40 decimals)")
    for m in range(3, 10):
        print(f"{m:>5}  {nstr(A1[m], 42)}")

    print("\nIncrements Delta_m = lam_m - lam_(m-1) and ratio Delta_m / Delta_(m-1)^2")
    D = {m: A1[m] - A1[m - 1] for m in range(4, 10)}
    for m in range(4, 10):
        r = "" if m - 1 not in D else f"   ratio = {nstr(D[m] / D[m - 1] ** 2, 10)}"
        print(f"{m:>5}  {nstr(D[m], 8)}{r}")

    print("\nSplitting s_m = E root - A1 root and ratio s_m / s_(m-1)^2")
    s = {m: E[m] - A1[m] for m in range(3, 8)}
    for m in range(4, 8):
        r = "" if m - 1 not in s else f"   ratio = {nstr(s[m] / s[m - 1] ** 2, 8)}"
        print(f"{m:>5}  {nstr(s[m], 8)}{r}")

    print("\nlambda_9 =", nstr(A1[9], 100))
    print("|lambda_9 - lambda_8| =", nstr(abs(A1[9] - A1[8]), 6))
    print("NOTE: E roots are intentionally computed only through level 7 at 260 dps.")


if __name__ == "__main__":
    main()
