# Open Problems and Research Roadmap

This page distinguishes unresolved research questions from completed diagnostics. The current documented release is v2.2.1. Items below are not presented as solved.

## 1. Independent selection rule for the mass indices { #1-independent-selection-rule }

**Question.** Can an operator or boundary-condition invariant select \(n\in\{1,12,17,40\}\) independently of the masses used to identify the target set?

**Current status.** No selection rule has been found in the tested families. Protocol versions v1.1 and v1.2.1 were designed so that the decision threshold was reachable, but neither passed the criterion. The earlier v1.0 test could not reach the threshold even in its best possible case and is therefore not an informative negative.

**Work already recorded.** Generation twists, scalar vertex potentials and corner Dirichlet conditions, SG × S¹ with lattice and continuum circles, and a Sierpiński-carpet search. The carpet's initial apparent 4/4 match was reassessed against chance and the branch was abandoned.

**What would justify reopening the search.** A new operator family with an a-priori mathematical rationale, a new preregistration, null-only power analysis, and an explicit accounting of all previous configuration families. A derivation of the indices from an operator invariant would be stronger than another post-hoc match.

See the [selection-protocol audit](selection-protocol.md).

## 2. Finite-level convergence of the spectral exponent { #2-finite-level-convergence-of-the-spectral-exponent }

**Question.** Can a finite-level estimator recover the asymptotic spectral exponent robustly without depending materially on a chosen log-periodic window?

The theoretical value is \(d_s/2=\ln3/\ln5\approx0.6826\). Ordinary regression fits show finite-level and window bias. The repository reports that the level-9 chord estimator is within 0.1% of its stated comparison expression for \(N\ge1000\), while sliding-window fits still vary with window width and phase. These are not contradictory: one is a specific estimator result, while the broader robustness and convergence question remains open.

**Documented inertia counts.** Sparse-LU inertia computations reach level 10 (88,575 vertices). For the stated fixed three-log-period window, the reported exponent deviations are −2.19% (level 6), −0.61% (level 7), +0.07% (level 8), +0.32% (level 9) and +0.41% (level 10). A level-9 sliding-window study still shows dependence on window width. Level 11 and above have not been tested in the documented run.

**Path forward.** Derive an analytical finite-size correction from decimation theory or establish an estimator whose output is stable under reasonable window choices. More levels alone are not expected to remove estimator-window dependence.

See [reproducibility instructions](reproducibility.md) and the source scripts in [protocol_data](https://github.com/RFT-SIRM/Phi-Genesis/tree/main/protocol_data).

## 3. Light fermions and a physical bridge

**Question.** Can the research define a model that addresses light fermions and independently connects the fitted scale to the electroweak scale?

The repository does not currently define a Lagrangian or beta functions for the proposed bridge, so an RG calculation is not yet specified. A toy NJL-type equation would introduce its own coupling and cutoff; these parameters must be counted against the number of masses explained. These items remain blocked until a concrete model is stated.

## Research discipline for the next phase

1. State the mathematical rationale before testing a new family.
2. Freeze the rule, null pools, statistic and decision threshold before evaluating targets.
3. Check power from null draws alone.
4. Count abandoned and exploratory searches in the cumulative ledger.
5. Label post-hoc analyses and dependencies between related operator families.
6. Keep a negative result bounded to the tested family and parameter range.

See [Methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md), [Protocol Ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md), and [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md).
