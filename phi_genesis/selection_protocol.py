"""Calibrated test for index-selection searches. Implements PREREGISTRATION.md v1.0 exactly.

Step A: python -m phi_genesis.selection_protocol stepA   (null pools and weights)
Step B: python -m phi_genesis.selection_protocol stepB   (evaluate the 75-configuration family)

Nothing here is tuned. Every constant is fixed by the pre-registration; changing one is a new
protocol version. A 'candidate' is NOT evidence for the mass formula (see PREREGISTRATION.md, section 6).
"""
import itertools
import json
import os
import sys

import numpy as np

from .sg_laplacian import sierpinski_graph

LEVEL = 5
TARGETS = (1, 12, 17, 40)
WINDOW = 60
K = 12
POOL_SIZE = 20000
WEIGHT_SPLIT = 10000
BOOTSTRAP_B = 10000
N_DECOYS = 200
ALPHA = 0.01
SEEDS = {"N-pot": 20261014, "N-edge": 20261015, "bootstrap": 20261016, "decoy": 20261017}
AMPLITUDES = (-3.0, -1.0, -0.3, -0.1, 0.1, 0.3, 1.0, 3.0)
CIRCLE_N = (3, 5, 8, 13)
CIRCLE_PHI = (0.0, 1 / 8, 1 / 4, 3 / 8, 1 / 2)
DATA_DIR = "protocol_data"

_cache = {}


def graph():
    """(coords, edges, adjacency A, corner indices) for the fixed level."""
    if "g" not in _cache:
        V, E, C = sierpinski_graph(LEVEL)
        n = len(V)
        A = np.zeros((n, n))
        E = np.array(E)
        A[E[:, 0], E[:, 1]] = 1.0
        A[E[:, 1], E[:, 0]] = 1.0
        _cache["g"] = (np.array(V, float), E, A, list(C))
    return _cache["g"]


def laplacian(A_signed=None, potential=None):
    coords, E, A, C = graph()
    L = np.diag(A.sum(axis=1)) - (A if A_signed is None else A_signed)
    if potential is not None:
        L = L + np.diag(potential)
    return L


def spectrum(L):
    return np.sort(np.linalg.eigvalsh(L))


def select(spec, k=K, window=WINDOW):
    """Rule R*: indices right after the k largest ratio jumps among the first `window` nonzero eigenvalues."""
    spec = np.sort(np.asarray(spec, float))
    nz = spec[spec > 1e-8][:window]
    ratios = nz[1:] / nz[:-1]
    top = np.argsort(ratios)[::-1][:k]
    return tuple(sorted((top + 1).tolist()))


# ----------------------------------------------------------------- null ensembles
def draw_pot(rng):
    coords = graph()[0]
    x, y = coords[:, 0], coords[:, 1]
    freq = rng.uniform(0.5, 8.0)
    scale = rng.uniform(0.2, 3.0)
    phase = rng.uniform(0.0, 2 * np.pi)
    a, b = rng.normal(size=2)
    return spectrum(laplacian(potential=scale * np.sin(freq * (a * x + b * y) + phase)))


def draw_edge(rng):
    A, E = graph()[2], graph()[1]
    q = rng.uniform(0.05, 0.5)
    flips = rng.random(len(E)) < q
    As = A.copy()
    As[E[flips, 0], E[flips, 1]] = -1.0
    As[E[flips, 1], E[flips, 0]] = -1.0
    return spectrum(laplacian(A_signed=As))


NULLS = {"N-pot": draw_pot, "N-edge": draw_edge}


def generate_pool(name, n, seed):
    rng = np.random.default_rng(seed)
    draw = NULLS[name]
    return [select(draw(rng)) for _ in range(n)]


# ----------------------------------------------------------------------- family
def family():
    """The 75 pre-registered configurations as (label, spectrum)."""
    coords, E, A, C = graph()
    x, y = coords[:, 0], coords[:, 1]
    u, v = x, y / (np.sqrt(3) / 2)
    corner = np.zeros(len(x))
    corner[C] = 1.0
    funcs = {
        "v": v,
        "u": u,
        "r2": (x - 0.5) ** 2 + (y - np.sqrt(3) / 6) ** 2,
        "cos2pi_u": np.cos(2 * np.pi * u),
        "cos2pi_v": np.cos(2 * np.pi * v),
        "corner": corner,
    }
    out = []
    for name, f in funcs.items():
        for c in AMPLITUDES:
            out.append((f"F1:{name}*{c:+g}", spectrum(laplacian(potential=c * f))))
    L0 = laplacian()
    for r in (1, 2, 3):
        for S in itertools.combinations(C, r):
            keep = [i for i in range(len(x)) if i not in S]
            out.append((f"F2:dirichlet{tuple(S)}", spectrum(L0[np.ix_(keep, keep)])))
    lam = spectrum(L0)
    for N in CIRCLE_N:
        for phi in CIRCLE_PHI:
            mu = 2 - 2 * np.cos(2 * np.pi * (np.arange(N) + phi) / N)
            out.append((f"F3:N={N},phi={phi:g}", np.sort((lam[:, None] + mu[None, :]).ravel())))
    return out


def family_selected():
    return [(lab, select(sp)) for lab, sp in family()]


# --------------------------------------------------------------------- statistics
def base_rates(pool):
    """Smoothed marginal rate of each index 1..WINDOW-1 in a pool of selected sets."""
    n = len(pool)
    cnt = np.zeros(WINDOW)
    for s in pool:
        for i in s:
            cnt[i] += 1
    return {i: (cnt[i] + 1) / (n + 2) for i in range(1, WINDOW)}


def weights(rates):
    return {i: -np.log(p) for i, p in rates.items()}


def score(sel, w, targets=TARGETS):
    return float(sum(w[i] for i in targets if i in sel))


def max_pvalue(null_scores, observed, M, B, seed):
    """P(max of M i.i.d. null scores >= observed), by resampling the pool of null scores."""
    rng = np.random.default_rng(seed)
    ns = np.asarray(null_scores, float)
    idx = rng.integers(0, len(ns), size=(B, M))
    mx = ns[idx].max(axis=1)
    return float((1 + np.sum(mx >= observed - 1e-12)) / (1 + B))


# --------------------------------------------------------------------------- steps
def step_a(out_dir=DATA_DIR, pool_size=POOL_SIZE):
    os.makedirs(out_dir, exist_ok=True)
    data = {"version": "1.0", "level": LEVEL, "window": WINDOW, "k": K, "pool_size": pool_size,
            "seeds": SEEDS, "pools": {}}
    for name in NULLS:
        data["pools"][name] = [list(s) for s in generate_pool(name, pool_size, SEEDS[name])]
    path = os.path.join(out_dir, "null_pools_v1.json")
    with open(path, "w") as fh:
        json.dump(data, fh)
    print("wrote", path)


def step_b(out_dir=DATA_DIR):
    with open(os.path.join(out_dir, "null_pools_v1.json")) as fh:
        data = json.load(fh)
    pools = {k: [tuple(s) for s in v] for k, v in data["pools"].items()}
    half = WEIGHT_SPLIT if len(next(iter(pools.values()))) >= 2 * WEIGHT_SPLIT else len(next(iter(pools.values()))) // 2
    fam = family_selected()
    M = len(fam)
    res = {"version": "1.0", "M": M, "targets": list(TARGETS), "configs": [], "nulls": {}}
    rng_d = np.random.default_rng(SEEDS["decoy"])
    decoys = [tuple([1] + sorted(rng_d.choice(np.arange(2, WINDOW), 3, replace=False).tolist()))
              for _ in range(N_DECOYS)]
    for name, pool in pools.items():
        w = weights(base_rates(pool[:half]))
        null_scores = [score(s, w) for s in pool[half:]]
        scores = [score(sel, w) for _, sel in fam]
        obs = max(scores)
        p = max_pvalue(null_scores, obs, M, BOOTSTRAP_B, SEEDS["bootstrap"])
        dec = [max(score(sel, w, targets=d) for _, sel in fam) for d in decoys]
        res["nulls"][name] = {"W_star": obs, "p": p, "weights_targets": {i: w[i] for i in TARGETS},
                              "base_rates_targets": {i: float(np.exp(-w[i])) for i in TARGETS},
                              "decoy_fraction_ge_target": float(np.mean(np.array(dec) >= obs - 1e-12))}
        res["configs"].append({"null": name, "scores": scores})
    res["configs_selected"] = [{"label": lab, "selected": list(sel),
                                "targets_hit": sorted(set(sel) & set(TARGETS))} for lab, sel in fam]
    res["max_targets_hit_any_config"] = max(len(set(sel) & set(TARGETS)) for _, sel in fam)
    res["candidate"] = all(v["p"] <= ALPHA for v in res["nulls"].values())
    path = os.path.join(out_dir, "results_v1.json")
    with open(path, "w") as fh:
        json.dump(res, fh, indent=1, default=float)
    print(json.dumps({k: res[k] for k in ("M", "max_targets_hit_any_config", "candidate")}))
    for name, v in res["nulls"].items():
        print(name, "W*=%.3f p=%.4f decoys>=target: %.3f" % (v["W_star"], v["p"], v["decoy_fraction_ge_target"]))
    print("wrote", path)


if __name__ == "__main__":
    {"stepA": step_a, "stepB": step_b}[sys.argv[1]]()
