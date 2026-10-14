"""Open Problem #2, exploratory: separate finite-level error from window bias in the Weyl exponent.

Estimators and windows are fixed here, before the run:
  grid   : 24 points per log-period (ln 5), sigma_k = exp(ln 0.375 - (k + 0.37) ln5/24), k = 0..144 (6 periods)
  window : W_j = [3e-3, 0.375] * 5^-j (3 log-periods), j = 0..3; j = 0 is the window used in the README
  E1     : OLS slope of ln N(sigma) vs ln sigma on the window
  E2     : same, with the first harmonic of the log-period added (columns 1, x, cos(2 pi x/ln5), sin(2 pi x/ln5))
  valid  : window W_j is valid at level L iff N_L(sigma_min of the window) >= 9 (no boundary of the finite graph)
Question: at fixed j, does the deviation converge in L (finite-level error), and does the limit shrink with j (window bias)?
Usage: python protocol_data/op2_window_bias.py counts 6 7 8 9   (computes and caches exact counts)
       python protocol_data/op2_window_bias.py table            (prints the table from the cache)
"""
import json
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from phi_genesis import sg_inertia as si  # noqa: E402

LN5 = np.log(5.0)
THEORY = si.THEORY_EXPONENT
PER = 24
K = 6 * PER
X = np.log(0.375) - (np.arange(K + 1) + 0.37) * LN5 / PER
SIGMA = np.exp(X)
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "op2_counts.json")
MIN_BELOW = 9


def load():
    return json.load(open(CACHE)) if os.path.exists(CACHE) else {}


def compute(levels):
    data = load()
    for L in levels:
        Lm, _ = si.sparse_laplacian(L)
        out = []
        for s in SIGMA:
            try:
                out.append(si.count_below(Lm, float(s)))
            except ValueError:
                out.append(-1)  # sigma too close to an eigenvalue: point dropped
        data[str(L)] = out
        json.dump(data, open(CACHE, "w"))
        print("level", L, "done; dropped points:", sum(v < 0 for v in out), flush=True)


def window_mask(j):
    lo, hi = np.log(3e-3) - j * LN5, np.log(0.375) - j * LN5
    return (X >= lo - 1e-9) & (X <= hi + 1e-9)


def estimators(x, lnN):
    e1 = np.polyfit(x, lnN, 1)[0]
    A = np.c_[np.ones_like(x), x, np.cos(2 * np.pi * x / LN5), np.sin(2 * np.pi * x / LN5)]
    e2 = np.linalg.lstsq(A, lnN, rcond=None)[0][1]
    return e1, e2


def table():
    data = load()
    print(f"theory exponent ln3/ln5 = {THEORY:.5f}; deviation = (estimate/theory - 1) in %")
    print("level  j  valid  points   E1 dev%   E2 dev%")
    for L in sorted(data, key=int):
        N = np.array(data[L], float)
        for j in range(4):
            m = window_mask(j) & (N > 0)
            valid = bool(m.sum() > 0 and N[m][-1] >= MIN_BELOW)  # largest-x end is sigma_max; check lowest sigma below
            lowest = np.where(m)[0].max()  # smallest sigma in window = largest index
            valid = N[lowest] >= MIN_BELOW
            if m.sum() < 12:
                print(f"{L:>5} {j:>2}  no     {m.sum():>5}")
                continue
            e1, e2 = estimators(X[m], np.log(N[m]))
            print(f"{L:>5} {j:>2}  {'yes' if valid else 'no ':<5} {m.sum():>5}  {100*(e1/THEORY-1):+8.2f}  {100*(e2/THEORY-1):+8.2f}")


if __name__ == "__main__":
    if sys.argv[1] == "counts":
        compute([int(a) for a in sys.argv[2:]])
    elif sys.argv[1] == "table":
        table()


# ---- Extension, added after the table above was seen (post hoc, labelled as such) -------------------------
def harmonic_slope(x, lnN, h):
    cols = [np.ones_like(x), x]
    for m in range(1, h + 1):
        cols += [np.cos(2 * np.pi * m * x / LN5), np.sin(2 * np.pi * m * x / LN5)]
    return np.linalg.lstsq(np.c_[tuple(cols)], lnN, rcond=None)[0][1]


def sliding(period_count=3):
    """All windows of `period_count` log-periods on the 6-period grid with N(lowest sigma) >= MIN_BELOW.
    For each estimator (h = 0: OLS; 1, 2, 3 harmonics) report mean, min, max of the deviation in %."""
    data = load()
    W = period_count * PER
    print(f"sliding windows of {period_count} periods; deviation % (mean [min, max]); h = number of harmonics")
    print("level  windows    h=0 (OLS)              h=1                   h=2                   h=3")
    for L in sorted(data, key=int):
        N = np.array(data[L], float)
        res = {h: [] for h in (0, 1, 2, 3)}
        for s in range(0, K - W + 1):
            idx = np.arange(s, s + W + 1)
            if N[idx[-1]] < MIN_BELOW or (N[idx] <= 0).any():
                continue
            for h in res:
                sl = np.polyfit(X[idx], np.log(N[idx]), 1)[0] if h == 0 else harmonic_slope(X[idx], np.log(N[idx]), h)
                res[h].append(100 * (sl / THEORY - 1))
        if not res[0]:
            print(f"{L:>5}  0")
            continue
        cells = [f"{np.mean(v):+6.2f} [{np.min(v):+6.2f},{np.max(v):+6.2f}]" for v in res.values()]
        print(f"{L:>5}  {len(res[0]):>6}   " + "  ".join(cells))


if __name__ == "__main__" and sys.argv[1] == "sliding":
    sliding()
