"""Exploratory: null pools storing the full ranking of ratio jumps, so any k can be derived.
Usage: python gen_rank_pool.py <N-pot|N-edge> <n> <seed> <out.npy>
Uses phi_genesis.selection_protocol draws; the family of 75 configurations is NOT touched.
"""
import sys

import numpy as np

sys.path.insert(0, "/home/claude/rft-sirm/phi-genesis")
from phi_genesis import selection_protocol as sp

name, n, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = np.random.default_rng(seed)
draw = sp.NULLS[name]
res = np.zeros((n, sp.WINDOW - 1), dtype=np.uint8)
for i in range(n):
    spec = np.sort(draw(rng))
    nz = spec[spec > 1e-8][: sp.WINDOW]
    ratios = nz[1:] / nz[:-1]
    res[i] = (np.argsort(ratios)[::-1] + 1).astype(np.uint8)  # positions, strongest jump first
    if (i + 1) % 10000 == 0:
        print(name, i + 1, flush=True)
np.save(out, res)
print("done", name, res.shape, flush=True)
