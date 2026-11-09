"""Numerical check of the quadratic increment law for the A1 roots of the Schur recursion.

Bisection for the A1 root of level n inside the 36-digit window, then
delta_{n+1} / delta_n^2 and |f'| / (2 lambda) at 800 digits.  Computational evidence only.
"""
from mpmath import mp, mpf, nstr

mp.dps = 800


def step(a, b, lam):
    c = 2 * a + lam - b
    den = c * (c + 3 * b)
    return a - 2 * b * b * (c + b) / den, -b * b * (c - b) / den


def traj(lam, n):
    a, b = 2 - lam, mpf(1)
    for _ in range(n):
        a, b = step(a, b, lam)
    return a, b


def f(lam, n):
    a, b = traj(lam, n)
    return a + 2 * b


L = mpf("1.309128920280813421888623088170810187")
U = mpf("1.309128920280813421888623088170810189")


def root(n):
    lo, hi = L, U
    for _ in range(2600):
        mid = (lo + hi) / 2
        if f(mid, n) >= 0:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def fprime(lam, n):
    h = mpf(10) ** (-300)
    return (f(lam + h, n) - f(lam - h, n)) / (2 * h)


prev_root, prev_delta = None, None
for n in range(6, 12):
    r = root(n)
    line = f"level {n}: f'(r) = {nstr(fprime(r, n), 12)}"
    if prev_root is not None:
        delta = r - prev_root
        line += f"  delta = {nstr(delta, 8)}"
        if prev_delta is not None:
            line += f"  delta/delta_prev^2 = {nstr(delta / prev_delta ** 2, 12)}"
        prev_delta = delta
    prev_root = r
    print(line)
print("|f'|/(2*lambda) =", nstr(abs(fprime(prev_root, 11)) / (2 * prev_root), 12))
