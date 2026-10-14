"""Protocol v1.1 (PREREGISTRATION_v1.1_DRAFT.md, committed d3605df). Implements it as written.

Only the constants listed in the v1.1 table differ from v1.0: selection size K = 6, pool size 100,000
(50,000 for weights + 50,000 for the null score distribution), new seeds. Graph, family, null ensembles,
statistic, bootstrap and decision rule are reused unchanged from selection_protocol.py (v1.0 code is not modified).

Step A: python -m phi_genesis.selection_protocol_v11 stepA
Step B: python -m phi_genesis.selection_protocol_v11 stepB
Step A must be committed (and pushed) before Step B is run.
A 'candidate' is NOT evidence for the mass formula (PREREGISTRATION.md section 6).
"""
import json
import os
import sys
from concurrent.futures import ProcessPoolExecutor

import numpy as np

from . import selection_protocol as sp

K = 6
WINDOW = sp.WINDOW  # 60
TARGETS = sp.TARGETS
POOL_SIZE = 100000
WEIGHT_SPLIT = 50000
BOOTSTRAP_B = sp.BOOTSTRAP_B  # 10,000
N_DECOYS = sp.N_DECOYS  # 200
ALPHA = sp.ALPHA  # 0.01
SEEDS = {"N-pot": 20270101, "N-edge": 20270102, "bootstrap": 20270103, "decoy": 20270104}
DATA_DIR = "protocol_data"


def select(spec):
    return sp.select(spec, k=K, window=WINDOW)


def _generate(args):
    name, n, seed = args
    rng = np.random.default_rng(seed)
    draw = sp.NULLS[name]
    return [select(draw(rng)) for _ in range(n)]


def step_a(out_dir=DATA_DIR, pool_size=POOL_SIZE):
    os.makedirs(out_dir, exist_ok=True)
    names = list(sp.NULLS)
    with ProcessPoolExecutor(max_workers=len(names)) as ex:
        pools = list(ex.map(_generate, [(nm, pool_size, SEEDS[nm]) for nm in names]))
    data = {"version": "1.1", "level": sp.LEVEL, "window": WINDOW, "k": K, "pool_size": pool_size,
            "seeds": SEEDS, "pools": {nm: [list(s) for s in pl] for nm, pl in zip(names, pools)}}
    path = os.path.join(out_dir, "null_pools_v1_1.json")
    with open(path, "w") as fh:
        json.dump(data, fh, separators=(",", ":"))
    print("wrote", path)


def step_b(out_dir=DATA_DIR):
    with open(os.path.join(out_dir, "null_pools_v1_1.json")) as fh:
        data = json.load(fh)
    assert data["k"] == K and data["version"] == "1.1"
    pools = {k: [tuple(s) for s in v] for k, v in data["pools"].items()}
    half = WEIGHT_SPLIT
    fam = [(lab, select(spec)) for lab, spec in sp.family()]
    M = len(fam)
    res = {"version": "1.1", "k": K, "M": M, "targets": list(TARGETS), "configs": [], "nulls": {}}
    rng_d = np.random.default_rng(SEEDS["decoy"])
    decoys = [tuple([1] + sorted(rng_d.choice(np.arange(2, WINDOW), 3, replace=False).tolist()))
              for _ in range(N_DECOYS)]
    for name, pool in pools.items():
        w = sp.weights(sp.base_rates(pool[:half]))
        null_scores = [sp.score(s, w) for s in pool[half:]]
        scores = [sp.score(sel, w) for _, sel in fam]
        obs = max(scores)
        p = sp.max_pvalue(null_scores, obs, M, BOOTSTRAP_B, SEEDS["bootstrap"])
        dec = [max(sp.score(sel, w, targets=d) for _, sel in fam) for d in decoys]
        res["nulls"][name] = {"W_star": obs, "p": p, "weights_targets": {i: w[i] for i in TARGETS},
                              "base_rates_targets": {i: float(np.exp(-w[i])) for i in TARGETS},
                              "decoy_fraction_ge_target": float(np.mean(np.array(dec) >= obs - 1e-12))}
        res["configs"].append({"null": name, "scores": scores})
    res["configs_selected"] = [{"label": lab, "selected": list(sel),
                                "targets_hit": sorted(set(sel) & set(TARGETS))} for lab, sel in fam]
    res["max_targets_hit_any_config"] = max(len(set(sel) & set(TARGETS)) for _, sel in fam)
    res["candidate"] = all(v["p"] <= ALPHA for v in res["nulls"].values())
    path = os.path.join(out_dir, "results_v1_1.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    print(json.dumps({k: res[k] for k in ("k", "M", "max_targets_hit_any_config", "candidate")}))
    for name, v in res["nulls"].items():
        print(name, "W*=%.3f p=%.4f decoys>=target: %.3f" % (v["W_star"], v["p"], v["decoy_fraction_ge_target"]))
    print("wrote", path)


if __name__ == "__main__":
    {"stepA": step_a, "stepB": step_b}[sys.argv[1]]()
