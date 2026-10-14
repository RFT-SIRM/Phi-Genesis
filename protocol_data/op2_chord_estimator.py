"""Open Problem #2, exploratory (theory-motivated): window-free chord estimator of the Weyl exponent.

Spectral decimation (phi(x) = x (5 - x)) holds for this Laplacian (corner degree 2) only up to corner-defect corrections;
in the points inspected N_{L+1}(s) = N_L(phi(s)) and N_{L+1}(s) = 3 N_L(s) - delta with delta <= 3 (not proven). Hence the chord exponent
    d(s) = ln( N_L(phi(s)) / N_L(s) ) / ln( phi(s) / s )
equals ln 3 / ln(5 - s) up to an O(1/N) counting offset, with no window and no phase; ln3/ln(5 - s) -> ln3/ln5 as s -> 0.
Output: deviation (%) of d(s) from the exact chord ln3/ln(5 - s), binned by N(s), on the sigma grid of op2_window_bias.py.
Usage: python protocol_data/op2_chord_estimator.py 8 9   (add 10 for level 10: about 15 minutes, 700 MB)
"""
import os
import sys

import numpy as np

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from phi_genesis import sg_inertia as si  # noqa: E402

LN5 = np.log(5.0)
TH = si.THEORY_EXPONENT
X = np.log(0.375) - (np.arange(0, 6 * 24 + 1) + 0.37) * LN5 / 24  # same grid as op2_window_bias.py
SIGMA = np.exp(X)
BINS = (10, 30, 100, 300, 1000, 3000)

if __name__ == "__main__":
    for L in [int(a) for a in sys.argv[1:]] or [8, 9]:
        Lm = si.sparse_laplacian(L)[0]
        rows = []
        for s in SIGMA:
            phi = s * (5.0 - s)
            try:
                a, b = si.count_below(Lm, float(s)), si.count_below(Lm, float(phi))
            except ValueError:
                continue
            if a <= 0:
                continue
            d = np.log(b / a) / np.log(phi / s)
            rows.append((a, s, 100 * (d / (np.log(3) / np.log(5 - s)) - 1)))
        R = np.array(rows)
        print(f"level {L}: chord estimate vs exact chord ln3/ln(5-sigma), deviation in %")
        for lo in BINS:
            m = R[:, 0] >= lo
            if m.sum():
                print(f"   N(sigma) >= {lo:>4}: {m.sum():>3} points  mean {R[m, 2].mean():+.3f}  range [{R[m, 2].min():+.3f}, {R[m, 2].max():+.3f}]")
