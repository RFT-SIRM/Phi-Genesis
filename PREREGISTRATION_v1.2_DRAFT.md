# Pre-registration v1.2 — DRAFT (design only; authorizes no evaluation)

**Status:** draft. Nothing under v1.2 has been evaluated. This file becomes binding only when committed and pushed.
It fixes the conditions that any further search must meet; it does not define a new family or rule yet. v1.0 and v1.1
and their results stay as they are.

## 1. Where v1.1 left the question

v1.1 (k = 6, window 60) could reach p <= 0.01 and returned *no evidence* for the 75-configuration family
(ledger row 5). Stage 1 is exhausted for these families. The top-quark index (about 1650) lies outside the window of 60.

## 2. Exploratory findings (not evaluations of the family; counted in the ledger as row 6)

`protocol_data/structure_check_exploratory.py` (plain SG Laplacian, levels 4-6):

- The degenerate-cluster structure of the first 60 nonzero eigenvalues is **identical at levels 4, 5 and 6**
  (cluster starts 1, 3, 4, 6, 8, 9, 10, 12, 15, 16, 18, 19, 21, 23, 27, 28, 30, 42, 46, ...). Low positions are a
  property of spectral decimation, not of the finite level.
- Of the targets {1, 12, 17, 40}: 1 and 12 are cluster starts; 17 is the second member of the pair [16, 17]; 40 lies
  inside the 12-fold cluster [30, 41]. A structural rule "positions that start a cluster" selects 2 of 4 targets,
  and 27 of the first 60 positions (45%) are cluster starts, so 2 of 4 is unremarkable.
- Conclusion: no structural rule on the plain SG tried here selects the target set.

## 3. Power of a top-quark test (arithmetic, not a measurement)

The top-quark index is not a single integer: the repo documents 1680, 1664 and 1654
(`test_top_quark_consistency.py`). If a rule selects k indices out of W candidate positions and a hit means
"any of the 3 candidate integers is selected", the null hit probability is about 3k/W. For k = 6 and
W = 3281 (nonzero eigenvalues of SG level 7) this is about 0.5%; but if the hit tolerance is widened to the whole range
1654-1680 (27 integers) it is about 4.9%, i.e. weight about 3 nats, similar to index 17 in v1.1. The more the target is
allowed to move, the less a top-quark hit is worth. A Stage-2 test must fix one integer (or a finite list) before
any evaluation and must state which.

## 4. Conditions for any v1.2 evaluation

An evaluation is authorized only after a v1.2.1 amendment is pushed that contains all four of:

1. a family of operators with an a-priori rationale (not chosen by trial against the targets);
2. a selection rule with fixed constants;
3. null-only pools (as in `power_by_k_design_v1_1.txt`) showing that the threshold p <= 0.01 is reachable by some
   outcome; if not, the test is not run;
4. a fixed target set, including the exact top-quark integer(s).

Cumulative search ledger carries over: 182 configuration evaluations after v1.1, plus 1 exploratory rule check
(row 6) = 183. Any later claim must correct for it.
