# Open Problems and Research Roadmap

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)

The central convergence theorem is established. The items below concern sharper evaluation, asymptotic structure, and extensions of the proved graph-matrix result. Separate physical-application questions are listed at the end and do not affect the principal theorem.

## 1. Sharper evaluation and analytic characterization of the limit

**Question.** Can the exact rational enclosure of $\lambda_\infty$ be sharpened to provide a certified decimal expansion at substantially higher precision, an effective error estimate for finite levels, or an analytic/algebraic characterization?

**Established starting point.** Lean proves that the least-eigenvalue sequence converges and that

$$
\lambda_\infty\in[L,U],\qquad U-L=2\cdot10^{-36}.
$$

This is already an exact existence-and-enclosure theorem. The approximately 145-digit output at level 9 is numerical and must not be substituted for a certified expansion of the infinite-level limit.

**Path forward.** Derive a quantitative tail estimate for $|\lambda_\infty-\lambda_N|$ that can be proved uniformly in $N$, then use outward-rounded interval arithmetic or exact rational bounds to sharpen the enclosure. Investigate closed-form or algebraic descriptions only as a further mathematical question; a closed form is not required for the limit to be a well-defined constant.

## 2. Prove the all-level quadratic increment law

**Question.** Do the increments $\delta_N=\lambda_N-\lambda_{N-1}$ satisfy

$$
\delta_{N+1}\sim c\,\delta_N^2
$$

for a rigorously defined coefficient $c$?

**Current evidence.** High-precision finite-level calculations show ratios approaching approximately $0.4939504899$ over the reported upper levels. The derivative recursion of the Schur trajectory is formalized, but the uniform derivative bounds and asymptotic argument needed to establish this law have not been proved.

**Path forward.** Establish uniform control of the differentiated Schur map along the root trajectory, identify the limiting coefficient, and prove a remainder estimate strong enough to justify the asymptotic relation.

## 3. Unconditional identification with the external $\theta=2\pi$ operator

**Question.** Can the recursively defined local-face matrix be identified source-to-source with the external operator denoted by $\theta=2\pi$?

The repository proves theorems for its explicitly defined graph matrices and their signed gauge realization. The physical/operator identification requires the external operator's source definition, boundary conventions, vertex/edge ordering, and a proof of exact equivalence. Numerical agreement alone is insufficient.

## 4. Complete spectral-decimation exceptional set

**Question.** Can the full recursive exceptional set for the implemented corner-degree-2 graph Laplacian be characterized, including all multiplicities and boundary corrections?

The map $\phi(\lambda)=\lambda(5-\lambda)$ captures the idealized decimation structure, but the graph's corner convention produces exceptional pairs and residuals that are not yet completely classified. The current diagnostics separate exact matches from near-misses and do not close the full correspondence.

## 5. Finite-level estimation of the spectral exponent { #2-finite-level-convergence-of-the-spectral-exponent }

**Question.** Can a finite-level estimator recover the asymptotic spectral exponent robustly without depending materially on a chosen log-periodic window?

The theoretical value is $d_s/2=\ln3/\ln5\approx0.6826$. Ordinary regression fits show finite-level and window bias. The level-9 chord estimator is within 0.1% of its stated comparison expression on the reported $N\geq1000$ subset, while sliding-window fits still vary with window width and phase. These are complementary results for different estimators; the broader robustness question remains open.

**Path forward.** Derive an analytical finite-size correction from decimation theory or establish an estimator whose output is stable under reasonable window choices. More levels alone are not expected to remove estimator-window dependence.

See [reproducibility instructions](reproducibility.md) and the source scripts in [protocol_data](https://github.com/RFT-SIRM/Phi-Genesis/tree/main/protocol_data).

## 6. Signed-$Z_2$ H10: prove the observed generation recurrence

**Question.** Can the finite-data relation

$$
F_{m+1}(t_1,\ldots,t_{m+1})
=3F_m(t_1,\ldots,t_m)+Q(t_1,t_2,t_3,t_{m+1})
$$

be derived for every level from copy restrictions, corner-moment identities, and the three-copy word expansion?

Exact generation-mask sweeps at levels 4–9 and 1,008 transition checks support one Boolean correction polynomial. At level 10, 156 directly computed masks agree with the recurrence. These checks do not prove the recurrence at arbitrary levels or constitute a Lean 4 formalization. Hole-boundary parities do not determine the complete signed cocycle; local representative choices affect H10.

**Path forward.** Prove the local restriction identities uniformly in the level, derive the correction polynomial from the word expansion, and formalize the resulting induction. Keep the representative convention explicit.

See the [finite H10 research note](higher-moments-z2.md).

## Separate historical application: spectral selection for a mass-fit model { #1-independent-selection-rule }

An earlier research branch explored whether independently motivated spectral constructions could select the integer labels used in a mass-fit study. The tested protocols, null ensembles, exploratory diagnostics, and their limitations are preserved in the [selection-protocol archive](selection-protocol.md), [D₃ audit](d3-representation-audit.md), [methodology](methodology.md), and [protocol ledger](protocol-ledger.md).

This application is logically separate from the Schur recursion and the proof of $\lambda_\infty$. Its hypotheses and statistical tests are not premises or dependencies of the convergence theorem. The archive remains available for historical completeness and any future independently motivated continuation.
