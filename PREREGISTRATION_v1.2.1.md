# Pre-registration v1.2.1 — SG x S^1 with spin structure (binding once committed and pushed, before Step A)

Follows `PREREGISTRATION_v1.2_DRAFT.md` (7380492) and satisfies its section 4. Nothing under v1.2.1 has been
evaluated against the targets. v1.0, v1.1 and their results stay as they are.

## 1. Family (10 configurations)

Operator `L_SG (x) 1 + 1 (x) (-d^2/dtheta^2)` on the level-5 gasket graph times a continuum circle of radius R. Eigenvalues:
`lambda_i + ((n + phi) / R)^2`, n in Z (modes |n| <= 100 kept; checked sufficient in `test_selection_protocol_v121.py`).

- phi in {0, 1/2}: periodic and antiperiodic spin structure on the circle (the two spin structures of S^1).
- R^2 = 5^j, j in {-2, -1, 0, 1, 2}: decimation multiplies SG eigenvalues by 5, which a circle matches by R^2 -> R^2 / 5.
- M = 5 x 2 = 10 configurations. The ranges of j and the values of phi were fixed by this rationale, not by trial.

**Disclosure.** Family F3 of v1.0 / v1.1 already used a lattice circle (N points, flux phi) on the same gasket. This family
is its continuum counterpart, so its result is not independent of F3's. The ledger will count 10 further evaluations
(cumulative 183 -> 193).

**Dirac vs Laplacian.** The ratio rule depends only on the order of ratios of consecutive eigenvalues, which is
unchanged by monotone maps of the spectrum (tested). A Dirac operator whose square is this operator selects the same
indices, so it is not a separate family under this rule.

## 2. Rule, graph, targets

Rule R*_8: indices (1-based position after the jump) of the **8** largest ratios among consecutive nonzero values
(> 1e-8), first 60 values. Window 60, SG level 5, targets T = {1, 12, 17, 40}: as in v1.0 / v1.1.

## 3. Choice of k (made from null draws only)

`protocol_data/power_design_v1_2_1.py` -> `power_design_v1_2_1.txt` (design seeds 20271101, 20271102; the family is never
evaluated). p is for M = 10; a pattern is a subset of T selected by one configuration.

| k | N-circ: patterns reaching p <= 0.01 | N-circpot: patterns reaching p <= 0.01 |
|---|---|---|
| 6 | {40} and every pattern containing 40 | {17,40}, {1,17,40}, {12,17,40}, all four |
| 8 | {17,40}, {1,17,40}, {12,17,40}, all four | {12,17,40}, all four |
| 12 | none (all four: p = 0.0122) | none (all four: p = 0.0172) |

k = 8 is the largest tested value for which the threshold is reachable in **both** nulls (all four: p = 0.0001 and
0.0007, floors set by the design pool sizes), and in both it requires at least {12, 17, 40}. k = 6 would let a single hit on
index 40 pass N-circ. The final pools are larger (100,000 draws per null).

## 4. Everything else

| Item | Value |
|---|---|
| Nulls | **N-circ**: plain SG spectrum x circle, log_5 R ~ U(-2, 2), phi ~ U(0, 1). **N-circpot**: SG with random oscillatory potential (v1.0 N-pot) x same circle |
| Pools | 100,000 draws per null: first 50,000 give base rates and weights, last 50,000 give the null score distribution |
| Seeds | N-circ 20271201, N-circpot 20271202, bootstrap 20271203, decoys 20271204 |
| Statistic, weights, max over M, bootstrap B = 10,000, decoys | as in v1.0 section 5 (`selection_protocol.py`, unchanged) |
| Decision | candidate iff p <= 0.01 in **both** nulls |

## 5. Commitments and limits

- Order: this file, the code and the design are committed and pushed; then Step A (pools) is committed and pushed; then
  Step B. Negative results are committed to the ledger as row 7.
- This tests the four light targets only. The top-quark index is not addressed (no single integer is fixed; see v1.2 draft section 3).
- The targets were derived from the same masses; "candidate" means only that a configuration deserves a Stage-2 test,
  not support for the mass formula (v1.0 section 6 applies unchanged).
- Any later claim must correct for the cumulative count of configuration evaluations in `protocol_ledger.md`.
