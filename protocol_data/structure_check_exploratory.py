"""EXPLORATORY (not pre-registered, not a v1.x evaluation). Cluster structure of the plain SG Laplacian.

Question: are the target positions {1, 12, 17, 40} (1-based among nonzero eigenvalues) structurally
special in the exact spectrum (starts of degenerate clusters)? Run: python protocol_data/structure_check_exploratory.py
"""
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
from phi_genesis import selection_protocol as sp

TARGETS = (1, 12, 17, 40)
WINDOW = 60


def clusters(level):
    sp.LEVEL = level
    sp._cache.clear()
    nz = sp.spectrum(sp.laplacian())
    nz = nz[nz > 1e-8]
    out, i = [], 0
    while i < len(nz):
        j = i
        while j + 1 < len(nz) and abs(nz[j + 1] - nz[i]) < 1e-8:
            j += 1
        out.append((i + 1, j + 1))  # 1-based first/last position of the cluster
        i = j + 1
    return out


if __name__ == "__main__":
    ref = None
    for L in (4, 5, 6):
        cl = [c for c in clusters(L) if c[0] <= WINDOW]
        starts = [a for a, _ in cl]
        if ref is None:
            ref = starts
        print(f"level {L}: cluster starts in window {WINDOW}: {starts}  (same as level 4: {starts == ref})")
    for t in TARGETS:
        a, b = next((a, b) for a, b in cl if a <= t <= b)
        print(f"target {t}: in cluster [{a},{b}] (multiplicity {b-a+1}); is a start: {t == a}")
    n_starts = len(ref)
    print(f"{n_starts} cluster starts below position {WINDOW}; targets that are starts: "
          f"{[t for t in TARGETS if t in ref]}")
