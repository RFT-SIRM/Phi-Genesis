# Pre-registration v1.0 — a calibrated test for index-selection searches (Open Problem #1)

**Status:** fixed before any evaluation of the families below. The git history of this file and of
`phi_genesis/selection_protocol.py` is the timestamp: Step A and Step B results (below) may only be
committed *after* this commit. Any later change to this document is a new version (v1.1, ...) and
everything computed under it is labelled exploratory.

## 1. What is being tested, and what is not

The integer indices {1, 12, 17, 40} come from fitting four measured masses (mu, c, tau, b) with one
free scale `A = 104.63 MeV`. They were fixed *after* the data. Therefore:

- a family of operators that happens to select them is **not evidence** for the mass formula;
- the existing twist-by-generation search (32 configurations, README section 3) already failed: at most 1 of 4
  targets, index 40 never selected. No operator is currently known that produces the targets.

This protocol tests something narrower and well-defined: **given a new family of operators, does it select
the target indices more strongly than a generic search of the same size would, after correcting for the number
of configurations tried?** It controls the look-elsewhere effect; it does not validate the mass formula.

## 2. Fixed choices (no free parameters left to the analyst)

| Item | Value |
|---|---|
| Graph | Sierpinski gasket, level `L = 5` (366 vertices), `phi_genesis.sg_laplacian.sierpinski_graph` |
| Gap rule R* | nonzero eigenvalues (`> 1e-8`), sorted, first `WINDOW = 60`; ratios of consecutive values; indices (1-based position after the jump) of the `K = 12` largest ratios. Identical to `sg_index_triviality.gap_selected_indices` |
| Targets | T = {1, 12, 17, 40} |
| Pool size | 20,000 draws per null ensemble (first 10,000 for weights, last 10,000 for the null score distribution) |
| Resamples | B = 10,000 |
| Seeds | N-pot 20261014, N-edge 20261015, bootstrap 20261016, decoys 20261017 |

## 3. Families (finite, fully listed; M = 75 configurations)

Let `u = x`, `v = y/(sqrt(3)/2)` (unit-triangle coordinates), `L0 = D - A` the plain Laplacian.

- **F1, structured scalar potentials (48):** `L0 + c * diag(f)` with `f` in {`v`; `u`; `(x-0.5)^2 + (y-sqrt(3)/6)^2`; `cos(2*pi*u)`; `cos(2*pi*v)`; corner indicator (3 corners)} and
  `c` in {-3, -1, -0.3, -0.1, 0.1, 0.3, 1, 3}.
- **F2, Dirichlet on corner subsets (7):** `L0` with rows/columns of every non-empty subset of the 3 corners removed.
- **F3, SG x twisted circle (20):** spectrum `lambda_i + mu_j`, `mu_j = 2 - 2*cos(2*pi*(j + phi)/N)`, `N` in {3, 5, 8, 13},
  `phi` in {0, 1/8, 1/4, 3/8, 1/2}.

**Excluded from v1 (declared, not forgotten):** mixed boundary conditions other than corner-Dirichlet, other fractals
(the carpet was already audited and abandoned in this repo; no other generator exists), the Z2 twist-by-generation family
(already tested under a different rule). Adding any of them is a later version.

## 4. Null ensembles

Each draw is one operator from a generic family; the same rule R* is applied.

- **N-pot (as in `sg_index_triviality`):** `V = s*sin(f*(a*x + b*y) + p)` with `f ~ U(0.5, 8)`, `s ~ U(0.2, 3)`, `p ~ U(0, 2*pi)`, `(a, b) ~ N(0, 1)^2`, added to `L0`.
- **N-edge (Z2 gauge noise):** `L = D - A_s`, where each edge sign is flipped independently with probability `q ~ U(0.05, 0.5)` drawn once per draw.

Both are required because the result must not depend on a single arbitrary notion of "generic".

## 5. Statistic and decision rule

1. **Weights (Step A).** From the first 10,000 draws of each null: `p_i = (count_i + 1)/(10,000 + 2)` for every index `i`, and `w_i = -ln p_i`. Index 1 (base rate ~95%) therefore carries little weight; rare indices carry much.
2. **Score** of a configuration with selected set S: `W(S) = sum of w_i over i in S ∩ T`.
3. **Observed statistic:** `W* = max over the 75 configurations of W`.
4. **Null distribution of the maximum:** score the last 10,000 draws of the null; draw 75 of them with replacement, take the maximum; repeat B = 10,000 times. This treats the 75 configurations as independent, which overstates the null maximum when the configurations are correlated, so **the test is conservative**.
5. **p-value:** `(1 + #{null max >= W*}) / (1 + B)`, computed separately against N-pot and N-edge.
6. **Decision:** the family is declared a **candidate** iff **both** p-values are `<= 0.01`. Otherwise: **no evidence**. Both outcomes are reported.

**Diagnostics (reported, not part of the decision):**
(a) the per-configuration table (selected set, score);
(b) decoys: the same pipeline with 200 random 4-sets `{1} ∪ 3 random indices from 2..59` in place of T. If T does not stand out against the decoys, any "hit" reflects the family's generic structure;
(c) the maximum number of targets simultaneously selected by any configuration.

## 6. What a "candidate" would and would not mean

A candidate would mean only that a specific configuration deserves a Stage-2 test. It would **not** support the mass formula,
because T was derived from the same masses it is meant to explain.

**Stage 2 (confirmation) is not testable today** and is listed only so that nobody mistakes Stage 1 for it:
(i) the selected set must be stable across levels 5, 6 and 7 with the rule unchanged;
(ii) the same operator must predict, before looking, the top-quark index `n_t = m_t / A` (about 1650; README section 7 documents that the
current estimates 1680, 1664, 1654 are mutually inconsistent). Rule R* has a 60-eigenvalue window and can never select an index near 1650, so (ii) needs a
different rule, to be fixed in a new version of this document *before* any Stage-2 evaluation.

## 7. Commitments

- Everything computed is committed, including negative results (`protocol_data/`, `protocol_ledger.md`).
- Order: **Step A** (null pools and weights) is committed before **Step B** (family evaluation).
- Any deviation (bug fix, changed parameter) is recorded in `protocol_ledger.md` as a deviation, and the affected results are labelled exploratory.
- Search ledger: `protocol_ledger.md` lists every family tried so far. Any later claim must correct for the cumulative number of configurations, not only the 75 of this version.
