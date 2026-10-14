# Search ledger (cumulative; every family ever tried against the targets {1, 12, 17, 40})

| # | Family | Configurations | Rule | Outcome |
|---|---|---|---|---|
| 1 | Z2 twist by generation (`mobius_selection_search`), level 5 | 32 | `mobius.gap_selected_indices`, k = 8 on relative gaps, whole spectrum | max 1 of 4 targets; index 40 never selected (README section 3) |
| 2 | Sierpinski carpet oscillator (`test_carpet_lookelsewhere.py`) | about 128 configurations at level 3 plus an unrecorded level-4 sweep (from the docstrings of `sierpinski_carpet.py` and `test_carpet_lookelsewhere.py`) | gap rule | A "4/4" match was reported; the null test shows the four hits are statistically independent and that >= 3/4 hits occur by chance in about 11% of random trials (4/4 in about 0.1%), consistent with a look-elsewhere effect. Branch abandoned (README). This search is **not** included in the cumulative counts of rows 5-7, which are therefore lower bounds: the true cumulative number is at least about 321. |
| 3 | Random oscillatory potentials on SG (`sg_index_triviality`) | audit of base rates, not a search | ratio rule, k = 12, window 60 | index 1 near-universal (~95%), index 40 ~3.4% (README section 8) |
| 4 | Protocol v1.0: F1 + F2 + F3 | 75 | rule R* (k = 12, window 60) | **no evidence** (commit c7e0c7f). W* = 3.538 (p = 0.922, N-pot), 3.197 (p = 0.968, N-edge); candidate threshold p <= 0.01 on both not met. Max 3 of 4 targets in one configuration (F3: N=13, phi=0.375, hits {1, 12, 17}; index 40 not selected). Index 40 hit by 4 of 75 configurations (expected ~2.3 from the N-pot base rate 3.0%). Decoys: T scores >= the target in 86% (N-pot) / 71.5% (N-edge) of 200 random 4-sets, i.e. T does not stand out. |
| 5 | Protocol v1.1: same F1 + F2 + F3 family, k = 6 (`PREREGISTRATION_v1.1_DRAFT.md` d3605df; Step A e9ffe15) | 75 | rule R*_6 (k = 6, window 60) | **no evidence**. W* = 3.268 (p = 0.966, N-pot), 2.604 (p = 0.997, N-edge); threshold p <= 0.01 on both not met. Max 2 of 4 targets in any configuration; index 40 selected by 0 of 75 configurations (N-pot base rate 0.7%), index 17 by 2, index 12 by 13. No configuration selected {12, 17, 40} or all four, the patterns that would have reached the threshold. Decoys: random 4-sets score >= T in 83% (N-pot) / 86.5% (N-edge). Unlike v1.0, this test could reach p <= 0.01 (minimum 0.0015 / 0.003), so this negative is informative about the 75 configurations. Cumulative configuration evaluations: 32 + 75 + 75 = 182. |
| 6 | Exploratory (not pre-registered): cluster-start rule on the plain SG Laplacian, levels 4-6 (`protocol_data/structure_check_exploratory.py`) | 1 | positions that start a degenerate cluster, window 60 | Selects 2 of 4 targets ({1, 12}); 27 of 59 positions are starts, so unremarkable. Cluster structure is identical at levels 4, 5, 6. Cumulative configuration evaluations: 183. |
| 7 | Protocol v1.2.1: SG x S^1 with spin structure, phi in {0, 1/2}, R^2 = 5^j, j in -2..2 (`PREREGISTRATION_v1.2.1.md` 1d9ed45; Step A 1a71e0c) | 10 | rule R*_8 (k = 8, window 60) | **no evidence** (commit 3b7fa82). W* = 1.598 (p = 0.953, N-circ), 1.846 (p = 0.926, N-circpot); threshold p <= 0.01 on both not met. Max 1 of 4 targets in any configuration (index 12, selected by all five phi = 1/2 configurations; indices 1, 17, 40 never selected). Only 6 distinct selected sets among the 10 configurations. Decoys: random 4-sets score >= T in 60% (N-circ) / 67% (N-circpot). The test could reach p <= 0.01 (design: all four give p = 0.0001 / 0.0007), so this negative is informative about these 10 configurations. This family is the continuum counterpart of F3 and not independent of it. Cumulative configuration evaluations: 183 + 10 = 193. |

Deviations from the pre-registration will be listed below with date and reason.

(none yet)

## Post-hoc diagnostics (exploratory; not part of the v1.0 decision)

**Power of the v1.0 test (2026-10-14).** Step B reproduces from `selection_protocol.stepB` on the committed
pools (selected sets identical; scores differ at the 1e-17 level only). Using the committed pools and weights, the
p-value that each possible hit pattern on T would have received, with M = 75:

| Hit pattern | p (N-pot) | p (N-edge) |
|---|---|---|
| {1, 12, 17, 40} (all four) | 0.136 | 0.216 |
| {12, 17, 40} | 0.150 | 0.274 |
| {17, 40} | 0.405 | 0.623 |
| {1, 40} (best observed pattern containing 40) | 0.922 | 0.968 |

**Even a configuration selecting all four targets would not reach p <= 0.01.** About 0.2% of generic null draws
already select all four targets (null scores reach W = 5.99 at the 99.99% quantile), and the maximum over 75 such draws
reaches that score in 14-22% of resamples. The v1.0 test therefore could not return "candidate" for any outcome:
its "no evidence" verdict is correct but carries no information about whether the family contains a selection
mechanism. The cause is rule R* (k = 12 of 59 positions), whose base rates for the targets are too high
(1: 96%, 12: 38%, 17: 23%). A later version must change the rule or the statistic so that the best possible
outcome can reach the threshold, and must fix that choice before evaluating any family.
