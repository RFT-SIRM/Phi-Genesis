# Pre-registration v1.1 — DRAFT (not in force until committed and pushed, before any v1.1 evaluation)

**Status:** draft. It becomes binding only when this file is committed *and pushed* before Step A and Step B of v1.1
are run. Everything computed under it before that moment is exploratory. v1.0 (`PREREGISTRATION.md`) and its
results stay as they are.

## 1. Why v1.1

A post-hoc power check (`protocol_ledger.md`, "Post-hoc diagnostics") showed that the v1.0 test could not reach
p <= 0.01 for any outcome: rule R* with k = 12 selects the four targets in about 0.2% of generic null draws, so even
a configuration selecting all four targets gets p = 0.14 (N-pot) / 0.22 (N-edge). A negative result from such a test
carries no information. v1.1 changes only what is needed to remove this defect.

## 2. What changes, and what does not

| Item | v1.0 | v1.1 |
|---|---|---|
| Selection size k | 12 | **6** |
| Window, graph, level, targets T | 60, SG L=5, {1,12,17,40} | unchanged |
| Family (75 configurations F1+F2+F3) | as listed | unchanged |
| Null ensembles N-pot, N-edge | as listed | unchanged, **new pools** |
| Pool size | 20,000 (10,000 + 10,000) | **100,000 (50,000 weights + 50,000 null scores)** |
| Statistic, weights, max over M, bootstrap B | as in v1.0 section 5 | unchanged |
| Decision | candidate iff both p <= 0.01 | unchanged |
| Seeds | 20261014..17 | **N-pot 20270101, N-edge 20270102, bootstrap 20270103, decoys 20270104** |

Rule R*_6: the indices (1-based position after the jump) of the **6** largest ratios among consecutive nonzero
eigenvalues (> 1e-8), first 60 values.

## 3. Choice of k (made from null ensembles only)

Chosen from `protocol_data/power_by_k_design_v1_1.txt`, which uses only null draws (seeds 20261101, 20261102) and
never evaluates the 75-configuration family. Per-draw null probability of selecting all four targets, and the
resulting minimum achievable p for M = 75:

| k | min p, N-pot (all four) | min p, N-edge (all four) | what is enough for p <= 0.01 |
|---|---|---|---|
| 12 | 0.094 | 0.195 | nothing (v1.0) |
| 8 | 0.003 | 0.018 | N-edge: nothing |
| 6 | 0.0015 | 0.003 | {12,17,40} or all four, in both nulls |
| 5 | 0.0015 | 0.0015 | N-edge: {1,17,40}, {12,17,40} or all four |
| 4 | 0.0015 | 0.0015 | N-pot also accepts {12,40}, {17,40} |

k = 6 is the largest tested value for which the threshold is reachable in **both** nulls and that still requires at
least three targets including index 40. The floor 0.0015 is the resolution of 50,000 null scores, not a measured
probability. Index 1 stays nearly uninformative at every k (base rate 0.66–0.92).

## 4. Commitments

- k, window, family, pools, seeds and the decision rule above are fixed before any evaluation of the family under k = 6.
  The family has not been evaluated under any k other than 12.
- Order: Step A (pools, weights) is committed before Step B (family evaluation). Negative results are committed.
- Cumulative search ledger: the 75 configurations re-evaluated under a different rule count as a new search.
  Cumulative count after v1.1: 32 + 75 + 75 = 182 configuration evaluations; any later claim must correct for it.
- A "candidate" still means only that a configuration deserves a Stage-2 test, not support for the mass formula
  (v1.0 section 6 applies unchanged, including that the targets were derived from the same masses).
