# Open Problems and Research Roadmap

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


This page distinguishes unresolved research questions from completed diagnostics. The current documented release is v2.2.1. Items below are not presented as solved.

## 1. Independent selection rule for the mass indices { #1-independent-selection-rule }

**Question.** Can an operator or boundary-condition invariant select \(n\in\{1,12,17,40\}\) independently of the masses used to identify the target set?

**Status (7 November 2026).** The documented finite search phase is frozen with a bounded negative result; the general mathematical question remains open.

**Current evidence.** No independently justified rule has been found in the documented generation-twist, potential/boundary/lattice-circle, continuum-circle/spin-structure, or carpet families. v1.0 was an uninformative negative because its threshold was unreachable; v1.1 and v1.2.1 had reachable thresholds and returned informative negatives within their declared families.

The corrected exploratory D₃ audit uses 1-based positive-spectrum ranks (zero mode removed). At levels 5, 6, and 7 the first-60 cluster signature agrees numerically. The target clusters are: 1 in [1,2] with representation E; 12 in [12,14] with A1 + E; 17 in [16,17] with E; 40 in [30,41] with 3A1 + A2 + 4E. “Contains A1” hits only 12 and 40 and selects whole clusters; “simple A1” hits none. This corrects the previous exploratory report's off-by-one error from including the zero mode.

**v1.3 archive.** A prior-session summary reports an ancestry/decimation probe, but its ZIP/source/data are not present in the inspected repository state. Its results remain pending independent verification and are not counted as verified.

**Conclusion boundary.** The finite search has not produced an independent selection rule. This is not a theorem that such a rule is mathematically impossible or that every conceivable operator family has been exhausted. The mass formula remains a numerical fit, not a spectral prediction.

**Reopening condition.** Verify the complete v1.3 archive, or preregister a new a-priori justified family with null-only power analysis, or derive the indices from an operator invariant independent of the masses. See [selection-protocol audit](selection-protocol.md) and [corrected D₃ audit](d3-representation-audit.md).

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

## 3. Signed-Z2 H10: prove the observed generation recurrence

**Question.** Can the finite-data relation
\[
F_{m+1}(t_1,\ldots,t_{m+1})=3F_m(t_1,\ldots,t_m)+Q(t_1,t_2,t_3,t_{m+1})
\]
be derived for every level from copy restrictions, corner-moment identities, and the three-copy word expansion?

**Current status.** Exact generation-mask sweeps at levels 4–9 and 1,008 transition checks support one Boolean correction polynomial. At level 10, 156 directly computed masks agree with the recurrence. These checks do not prove the recurrence at arbitrary levels or constitute a Lean 4 formalization. In addition, hole-boundary parities do not determine the complete signed cocycle: local representative choices affect H10.

**Path forward.** Prove the local restriction identities uniformly in the level, derive the correction polynomial from the word expansion, and formalize the resulting induction. Keep the representative convention explicit. Do not identify this scalar signed-graph result with the SU(2) trace-defect theorem.

See the [finite H10 research note](higher-moments-z2.md).

## Research discipline for the next phase

1. State the mathematical rationale before testing a new family.
2. Freeze the rule, null pools, statistic and decision threshold before evaluating targets.
3. Check power from null draws alone.
4. Count abandoned and exploratory searches in the cumulative ledger.
5. Label post-hoc analyses and dependencies between related operator families.
6. Keep a negative result bounded to the tested family and parameter range.

See [Methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md), [Protocol Ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md), and [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md).

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
