"""v1.2.1 design: choose k from NULL draws only (design seeds 20271101, 20271102); never evaluates the family.

For each k: base rates and weights of the targets (first half of the draws), the null probability q of the best
pattern scores (second half), and p for M = 10 configurations, p = 1 - (1 - q)^M with q floored at 1 / n_null.
Run: python protocol_data/power_design_v1_2_1.py > protocol_data/power_design_v1_2_1.txt
"""
import itertools
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from phi_genesis import selection_protocol as sp  # noqa: E402
from phi_genesis import selection_protocol_v121 as m  # noqa: E402

KS = (3, 4, 5, 6, 8, 12)
M = 10
import os as _os
DESIGN = {"N-circ": (20271101, 200000), "N-circpot": (20271102, 30000)}
if _os.environ.get("ONLY"):
    DESIGN = {k: v for k, v in DESIGN.items() if k == _os.environ["ONLY"]}
T = sp.TARGETS

for name, (seed, n) in DESIGN.items():
    rng = np.random.default_rng(seed)
    # draw the circle/spectrum parameters once and select with every k from the same operator
    sets = {k: [] for k in KS}
    for _ in range(n):
        if name == "N-circ":
            lam = m.plain_lam()
        else:
            lam = sp.draw_pot(rng)
        u = rng.uniform(*m.U_RANGE)
        phi = rng.uniform(0.0, 1.0)
        mm = ((m._N + phi) / 5.0 ** u) ** 2
        s = (lam[:, None] + mm[None, :]).ravel()
        small = np.sort(np.partition(s, m.KEEP)[:m.KEEP])
        for k in KS:
            sets[k].append(sp.select(small, k=k, window=m.WINDOW))
    half = n // 2
    print(f"\n=== {name}  (draws {n}, weights from first {half}, null scores from last {n - half}) ===")
    for k in KS:
        pool = sets[k]
        w = sp.weights(sp.base_rates(pool[:half]))
        sc = np.array([sp.score(s, w) for s in pool[half:]])
        pats = [c for r in range(1, 5) for c in itertools.combinations(T, r)]
        ok = []
        for c in pats:
            W = sum(w[i] for i in c)
            q = max(np.mean(sc >= W - 1e-12), 1.0 / len(sc))
            if 1 - (1 - q) ** M <= 0.01:
                ok.append(c)
        W4 = sum(w[i] for i in T)
        q4 = max(np.mean(sc >= W4 - 1e-12), 1.0 / len(sc))
        print(f"k={k:2d} weights T: " + ", ".join(f"{i}:{w[i]:.2f}" for i in T) + " | base rates: " +
              ", ".join(f"{i}:{np.exp(-w[i]):.3f}" for i in T))
        print(f"      all four: W={W4:.2f}  q={q4:.2e}  p(M={M})={1 - (1 - q4) ** M:.4f}")
        print(f"      patterns that would reach p<=0.01: {ok if ok else 'none'}")
