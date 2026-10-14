"""Exploratory: minimum achievable p of the v1.0 statistic for different selection sizes k.
Reads rank_pot.npy / rank_edge.npy (strongest jump first). Families are not evaluated.
"""
import itertools
import sys

import numpy as np

S = sys.argv[1]
T = (1, 12, 17, 40)
M = 75
WINDOW = 60
KS = (3, 4, 5, 6, 8, 12)
ALPHA = 0.01

for name, fn in (("N-pot", "rank_pot.npy"), ("N-edge", "rank_edge.npy")):
    R = np.load(f"{S}/{fn}")
    n = len(R)
    h = n // 2
    print(f"\n=== {name}  (draws {n}, weights from first {h}, null scores from last {n - h}) ===")
    for k in KS:
        sel = R[:, :k]
        mask = np.zeros((n, WINDOW), dtype=bool)
        np.put_along_axis(mask, sel.astype(np.int64), True, axis=1)
        cnt = mask[:h].sum(axis=0)
        w = -np.log((cnt + 1) / (h + 2))
        tw = {i: w[i] for i in T}
        null_scores = mask[h:][:, list(T)] @ np.array([tw[i] for i in T])
        rows = []
        for r in range(1, 5):
            for sub in itertools.combinations(T, r):
                W = sum(tw[i] for i in sub)
                c = int(np.sum(null_scores >= W - 1e-12))
                q = (c + 1) / (len(null_scores) + 1)  # upper-biased per-draw tail
                p = 1 - (1 - q) ** M
                rows.append((sub, W, c, q, p))
        full = rows[-1]
        ok = [r for r in rows if r[4] <= ALPHA]
        print(f"k={k:2d}  weights T: " + ", ".join(f"{i}:{tw[i]:.2f}" for i in T)
              + f" | base rates: " + ", ".join(f"{i}:{np.exp(-tw[i]):.3f}" for i in T))
        print(f"      all four: W={full[1]:.2f}  null hits {full[2]}/{len(null_scores)}  q={full[3]:.2e}  p(M=75)={full[4]:.4f}"
              + ("   <-- reaches 0.01" if full[4] <= ALPHA else ""))
        print("      patterns that would reach p<=0.01: " + (", ".join(str(r[0]) for r in ok) if ok else "none"))
