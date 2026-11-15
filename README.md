# Phi-Genesis — Schur Recursion and the Limiting Spectral Constant

[![Research programme](https://img.shields.io/badge/RFT--SIRM-Phi--Genesis-5b4bc4?style=for-the-badge)](https://github.com/RFT-SIRM/Phi-Genesis)
[![Python](https://img.shields.io/badge/Python-3.10%2B-3776AB?style=for-the-badge&logo=python&logoColor=white)](https://www.python.org/)
[![Tests](https://img.shields.io/badge/Tests-Pytest-168f83?style=for-the-badge&logo=pytest&logoColor=white)](https://github.com/RFT-SIRM/Phi-Genesis/actions)
[![Research history](https://img.shields.io/badge/Read-Research%20History-0f766e?style=for-the-badge)](https://rft-sirm.github.io/Phi-Genesis/history.html)

**Phi-Genesis is a mathematical and computational research project** on spectral operators on recursively refined Sierpiński-gasket graphs. Its principal result is an exact three-corner Schur recursion, formally connected to the graph matrices in Lean 4, together with a proof that the least-eigenvalue sequence converges to a precisely defined limit inside an exact rational interval of width $2\cdot10^{-36}$. The repository also preserves finite-level high-precision calculations and separate workstreams on spectral decimation, boundary conditions, spectral counting, and signed-graph moments.

> [!IMPORTANT]
> **Principal mathematical result:** for the specified Sierpiński-gasket graph matrices, Lean 4 proves that the least eigenvalue at every level $N\geq6$ is the unique selected $A_1$ Schur root in an exact rational interval $[L,U]$, and that these least eigenvalues converge to $\lambda_\infty\in[L,U]$.
>
> The interval has width $2\cdot10^{-36}$. The approximately 145-digit level-9 value is a finite-level numerical computation, not a 145-digit proof for the limit. The proof, numerical record, and remaining questions are collected in the [spectral-limit dossier](docs/spectral-limit.md).

<div align="center">

[**Browse the research map →**](https://rft-sirm.github.io/Phi-Genesis/research-map.html) · [**Read the dissertation →**](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)

</div>

---

## Contents

- [Schur recursion and limiting spectral constant](docs/spectral-limit.md)
- [At a glance](#at-a-glance)
- [Mathematical core](#mathematical-core)
- [Key numerical results](#key-numerical-results)
- [Exact finite H10 calculations](#exact-finite-h10-calculations-for-the-signed-z_2-flux-laplacian)
- [Lean 4 formalization](#lean-4-formalization-current-verified-scope)
- [Supplementary research archive](#supplementary-research-archive)
- [Test and reproducibility guide](#test-and-reproducibility-guide)
- [Repository map](#repository-map)
- [Research standards and citation](#research-standards-and-citation)

## At a glance

| Main question | Current result | Evidence |
|---|---|---|
| Does the exact Schur recursion describe the graph-matrix boundary response? | Yes, within the stated bootstrap interval; the scalar recursion is connected to the recursively defined graph matrices. | **LEAN 4 FORMALIZED** |
| Is the selected $A_1$ root the least eigenvalue? | Yes, uniquely in the exact interval for every level $N\geq6$. | **LEAN 4 FORMALIZED** |
| Does the least-eigenvalue sequence converge? | Yes. Its limit $\lambda_\infty$ lies in the exact rational interval $[L,U]$, of width $2\cdot10^{-36}$. | **LEAN 4 FORMALIZED** |
| Is the signed local-face matrix covered? | Yes. It is diagonally gauge-conjugate to the signless graph Laplacian and has the same spectrum. | **LEAN 4 FORMALIZED** |
| Is there a uniform positive lower bound? | Every real eigenvalue of the signed matrix is at least $1$ at every refinement level. | **LEAN 4 FORMALIZED** |
| What is the high-precision decimal? | The level-9 finite graph has a numerical value stable to about 145 displayed digits; these are not certified digits of $\lambda_\infty$. | **NUMERICAL** |
| What remains open? | A sharper certified evaluation or analytic identification of the limit, the all-level quadratic increment law, and unconditional identification with an external $\theta=2\pi$ operator. | **OPEN** |

### Evidence labels used here

| Label | Meaning |
|---|---|
| **FORMALIZED** | A stated proposition is accepted by a specified proof assistant and build. This label is not used for the numerical claims below. |
| **NUMERICALLY REPRODUCED** | A computation can be rerun for stated code, parameters, and finite inputs. It does not prove a universal theorem. |
| **CERTIFIED FINITE-LEVEL** | A certificate establishes a finite case or coefficient under stated bounds; it does not automatically prove all levels. |
| **NOT ESTABLISHED** | The available evidence does not establish the stronger claim. |
| **NOT REPRODUCED / REJECTED** | A named claim did not survive the documented reproduction attempt or conflicts with the reported checks. |
| **OPEN** | A derivation, proof, independent replication, or decisive experiment remains incomplete. |

---

## Evidence dashboard

### Central result: the limiting least eigenvalue

For $Q_N=D_N+A_N$, the exact Schur boundary recursion selects a unique $A_1$ root in the rational interval $[L,U]$ for each $N\geq6$. Lean proves that this root is the least eigenvalue and that the resulting sequence converges. The signed local-face realization $H_N=D_N+A_{s,N}$ is gauge-conjugate to $Q_N$, so the same least-eigenvalue result applies to it.

The interval endpoints and theorem dependencies are recorded in the [spectral-limit dossier](docs/spectral-limit.md) and [Lean proof map](computational/spectral_gap_theta_2pi/PROOF_MAP.md).

### Supporting research strands

- **Finite-level precision:** high-precision Schur calculations distinguish the $A_1$ ground state from the nearby $E$ doublet. The numerical output is kept separate from the Lean convergence theorem.
- **Spectral decimation and gaps:** the factor-five structure and Fukushima–Shima gap patterns are reproduced with the documented corner-defect qualifications.
- **Boundary conditions:** finite-graph $\pi$-flux calculations record how the spectrum responds to the specified twists.
- **Signed-$Z_2$ moments:** exact sparse-integer calculations are available through level 10 for the explicitly chosen representative; the observed recurrence is not yet an all-level theorem.
- **Additional physical applications:** exploratory fits and protocol records are preserved separately. They are not assumptions, inputs, or evidence for the Schur-limit theorem.

## Exact finite H10 calculations for the signed `Z_2`-flux Laplacian

The repository now includes a reproducible exact-integer computation module for the scalar signed operator:

<p>L<sub>m</sub> = D<sub>m</sub> − A<sub>s,m</sub>; &nbsp; D<sub>m</sub><sup>(10)</sup> = Tr(L<sub>π,m</sub><sup>10</sup>) − Tr(L<sub>0,m</sub><sup>10</sup>).</p>

Here the signs are the deterministic GF(2) representative produced by the project's hole-boundary solver (non-pivot edge variables set to zero). These results are **not** invariant under all cocycles with the same prescribed hole parities.

For this representative, exact sparse-integer calculations give:

| Level $m$ | Vertices | Edges | Holes | $D_m^{(10)}$ | $D_m^{(10)}-3D_{m-1}^{(10)}$ |
|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 9 | 1 | 19,523,880 | — |
| 2 | 15 | 27 | 4 | 178,774,440 | 120,202,800 |
| 3 | 42 | 81 | 13 | 548,852,760 | 12,529,440 |
| 4 | 123 | 243 | 40 | 1,658,945,640 | 12,387,360 |
| 5 | 366 | 729 | 121 | 4,989,224,280 | 12,387,360 |
| 6 | 1,095 | 2,187 | 364 | 14,980,060,200 | 12,387,360 |
| 7 | 3,282 | 6,561 | 1,093 | 44,952,567,960 | 12,387,360 |
| 8 | 9,843 | 19,683 | 3,280 | 134,870,091,240 | 12,387,360 |
| 9 | 29,526 | 59,049 | 9,841 | 404,622,661,080 | 12,387,360 |
| 10 | 88,575 | 177,147 | 29,524 | 1,213,880,370,600 | 12,387,360 |

The observed affine law is verified on levels 3 through 10 only:

<p><i>D</i><sub>m</sub><sup>(10)</sup> = 3 <i>D</i><sub>m−1</sub><sup>(10)</sup> + 12,387,360.</p>

It is a finite computational result, **not yet an all-level theorem**.

A second exact sweep evaluates every generation-twist mask at levels 4--9 (16, 32, 64, 128, 256, and 512 masks). All 1,008 transition checks from level 3 to 9 agree with the same Boolean correction $Q(t_1,t_2,t_3,t_{m+1})$. At level 10, 156 directly evaluated masks agree with the recurrence; the remaining masks at that level are predictions, not direct matrix-power calculations. The full correction polynomial, mathematical derivation route, finite audits, and caveats are in [the H10 research note](docs/higher-moments-z2.md).

**Evidence boundary.** Hole-boundary parities do not uniquely determine the signed cocycle. At level 5, the audit finds 243 remaining elementary-triangle holonomy degrees of freedom; changing the local representative while preserving the listed hole parities changes the tenth trace. The result is therefore a property of the specified representative, not a topological invariant of hole flux alone. The scalar signed operator is also distinct from the noncommutative SU(2) operator in [Evgeny-Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem); the central-lift trace identity does not by itself identify their H10 defects.

Reproduce with `python -m phi_genesis.higher_moments_z2 --validate-reference --max-level 10`; run `pytest -q test_higher_moments_z2.py` for regression checks. See [calculation instructions and data](computational/higher_moments_z2/README.md).

## Lean 4 formalization: current verified scope

The Lean 4 project is on `main` (package `PhiGenesis`, entry point `PhiGenesis.lean`) and is built by the `Lean formalization` workflow on every pull request.

- Lean toolchain: `leanprover/lean4:v4.33.1`.
- Mathlib: pinned by `lake-manifest.json` to revision `0df444a360eaa60ab8c11dca51a86af692955474`.
- Build target: `lake build PhiGenesis`.
- CI: [Lean formalization workflow](https://github.com/RFT-SIRM/Phi-Genesis/actions/workflows/lean.yml).
- Audit: no `sorry` and no user-declared axioms under `PhiGenesis/`. The theorems listed below depend only on `propext`, `Classical.choice` and `Quot.sound`.

| Block | What is formalized | Where |
|---|---|---|
| Incidence forests over GF(2) | Indexed incidence columns are linearly independent over `ZMod 2` if and only if every nonempty finite edge subset has a vertex of odd degree parity. | `PhiGenesis/H10/IncidenceForest.lean` |
| Vertex order of the gasket | The recursive vertex list, an explicit formula for level `n + 1` (`gasketVertexOrder_succ_explicit`), state A of the root cell at all levels (`gasketVertexOrder_stateA`), child cells A / A / B (`gasketVertexOrder_child0_cellA`, `gasketVertexOrder_child1_cellA`, `gasketVertexOrder_child2_cellB`), and concrete state orders at addresses 20 and 22 (`gasketVertexOrder_address22_cellB`). | `PhiGenesis/H10/GasketVertex*.lean` |
| Signed Laplacian | The signed Laplacian is identified with the Gram matrix of a signed incidence matrix, and every real eigenvalue with a nonzero real eigenvector is at least 1 at every level (`sgSignedLaplacianMatrix_eigenvalue_ge_one`). | `PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean` |

**Scope limitation.** In `IncidenceForest.lean`, `IsIncidenceForest` is defined by the odd-degree condition; its equivalence with the conventional graph-theoretic definition of a forest is not yet formalized. The vertex-order lemmas are purely combinatorial and say nothing about the spectrum. Still open: states B and C for cells of arbitrary depth, monotonicity of hypotenuses, the address tree and its cuts, and the finite certificates. The all-level H10 recurrence is **not** a Lean-verified theorem.

To reproduce the build:

~~~bash
lake build PhiGenesis
~~~

## Spectral gap at theta = 2 pi

For the explicit local-face operator `H = D + A_s` at the central twist angle, the full record is in [`computational/spectral_gap_theta_2pi/`](computational/spectral_gap_theta_2pi/README.md).

| Status | Statement |
|---|---|
| Proved in Lean 4 | Every real eigenvalue of the stated signed graph Laplacian is at least $1$ at every refinement level; the spectral gap therefore cannot close. |
| Computed numerically | The exact finite-level Schur recursion gives bottom-eigenvalue values $1.3091289186270032\ldots$ at level 4, $1.3091289202808134205\ldots$ at level 5, and $1.3091289202808134218886230881708101885523\ldots$ at level 9. The level-9 value is a finite-level numerical computation (about 145 displayed stable digits), not a 145-digit proof for the infinite-level limit. The observed quadratic ratios are numerical evidence only. See [the high-precision note](computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md). |
| Proved in Lean 4 | For every $N\geq6$, the least eigenvalue of the level-$N$ signless Laplacian and its gauge-conjugate signed matrix is the unique $A_1$ root in the exact rational interval $[L,U]$, and the sequence of these least eigenvalues converges to $\lambda_\infty\in[L,U]$. The interval has width $2\cdot10^{-36}$. See the [Lean proof map](computational/spectral_gap_theta_2pi/PROOF_MAP.md). |
| Computer-assisted finite-level result | Outward-rounded interval/inertia checks certify the $A_1$ ground state and $E$-sector first excited doublet for levels 1–12. This is a finite-level computer-assisted certificate, not a Lean theorem about all levels. |
| Open | An explicit closed form or a sharper rigorously certified decimal expansion of $\lambda_\infty$; a proof of the all-level quadratic increment law and its coefficient; and an unconditional identification of this local-face matrix model with the external $\theta=2\pi$ operator. |

Here $L$ and $U$ are exact rationals:

$$
L=\frac{1309128920280813421888623088170810187}{10^{36}},
\qquad
U=\frac{1309128920280813421888623088170810189}{10^{36}},
\qquad
\lambda_\infty\in[L,U].
$$

The convergence theorem proves that $\lambda_\infty$ exists and lies in this interval. It does **not** identify the limit with the 145-digit level-9 decimal expansion or provide a closed-form expression. The numerical level-9 result and the Lean convergence theorem are distinct pieces of evidence.
## Mathematical core

### 1. Sierpiński-gasket spectral decimation

The working decimation map is

$$
\boxed{\phi(\lambda)=\lambda(5-\lambda)}
$$

For the idealized decimation relation, inverse branches are used to compare candidate preimages across graph levels. In the actual implementation, the graph Laplacian has degree-2 corner vertices, and this boundary convention produces exceptional pairs and residuals that must be characterized rather than hidden.

**Gate A status:** some pairs match to floating-point machine precision; the simple exclusion of exceptional values $\{2,5,6\}$ does not account for every mismatch. The nightly diagnostic checks that the machine-exact subset really is exact at numerical precision and that its match rate increases across levels 5–7. This is evidence about the checked pairs and trend—not proof that the full decimation correspondence is closed.

- [Gate A diagnostic test](test_decimation_gate_a.py)
- [Residual-statistics tests](test_decimation_residual_summary.py)
- [Spectral decimation implementation](phi_genesis/sg_laplacian.py)
- [Fukushima–Shima checks](test_fukushima_shima.py)

### 2. Spectral dimension and the Weyl exponent

For the Sierpiński gasket, the theoretical exponent is

$$
\boxed{\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx0.682606}
$$

The counting function $N(\lambda)$ counts eigenvalues below a threshold $\lambda$, with the precise convention defined by the implementation. Finite-level regressions are sensitive to the fitting window because the counting staircase has log-periodic structure.

The exploratory chord estimator compares a count at $\sigma$ with a count at its decimation image $\phi(\sigma)$:

$$
\widehat{d_s/2}(\sigma)=
\frac{\ln\!\left[N(\phi(\sigma))/N(\sigma)\right]}
{\ln\!\left[\phi(\sigma)/\sigma\right]}
$$

Under the working count relation, this tends toward

$$
\frac{\ln 3}{\ln(5-\sigma)}
\longrightarrow
\frac{\ln 3}{\ln 5}
\qquad (\sigma\to0)
$$

**Reported numerical result:** at level 9, for the 14 sampled points with $N\ge1000$, the chord estimate differs from $\ln3/\ln(5-\sigma)$ by an average of about $-0.03\%$, with a range of approximately $-0.08\%$ to $+0.07\%$. This is an exploratory consistency check added after the regression study—not a preregistered discovery and not new physical evidence. The exact theoretical exponent itself is not in question; the open problem is stable finite-level estimation and full control of the corner correction.

- [Inertia counting implementation](phi_genesis/sg_inertia.py)
- [Window-bias experiment](protocol_data/op2_window_bias.py)
- [Chord-estimator experiment](protocol_data/op2_chord_estimator.py)
- [Open Problem #2 data and discussion](protocol_data/)

### 3. Boundary conditions and π-flux

The project also studies signed graph operators representing $Z_2$-flux / Möbius-style boundary twists. The reported level-5 full-$\pi$-flux calculation changes the first eigenvalue from approximately 0.006 to 0.46. Partial twists were also tested.

These finite-level experiments form a supporting boundary-condition workstream. They are distinct from the Schur-limit theorem and are not used as premises in its proof.

- [Signed-flux operator](phi_genesis/mobius.py)
- [Boundary-twist tests](test_mobius.py)

---

## Key numerical results

| Quantity | Reported result | Interpretation |
|---|---:|---|
| Limiting least eigenvalue | $\lambda_\infty\in[L,U]$, where $U-L=2\cdot10^{-36}$ | Exact Lean-proved enclosure |
| Level-9 bottom eigenvalue | $1.3091289202808134218886230881708101885523\ldots$ | Finite-level numerical calculation; not the limit's certified decimal |
| Quadratic increment ratio | Approximately $0.4939504899$ from the higher levels shown | Numerical observation only; the all-level law is open |
| Uniform signed spectral lower bound | $\lambda\geq1$ | Lean theorem for every refinement level |
| Theoretical spectral exponent | $d_s/2=\ln3/\ln5\approx0.6826$ | Theoretical reference value |
| Full $\pi$-flux first eigenvalue, level 5 | About 0.46 | Finite-level boundary-condition result |
| Signed-$Z_2$ tenth-moment residual | 12,387,360 on transitions 3→4 through 9→10 | Exact finite computation for the stated representative; no all-level theorem |

## Supplementary research archive

Phi-Genesis also preserves an earlier exploratory application that asked whether spectral constructions could independently select integer labels used in a mass-fit study. This is a separate physical-interpretation question; it is not part of the Schur-recursion argument and does not affect the definition, proof, or value enclosure for $\lambda_\infty$.

The complete historical record remains available without being placed at the centre of the project:

- [Selection protocol and versioned tests](docs/selection-protocol.md)
- [D₃ representation audit](docs/d3-representation-audit.md)
- [Methodology and statistical design](METHODOLOGY.md)
- [Cumulative protocol ledger](protocol_ledger.md)
- [Verified-results overview](docs/verified-results.md)

## Main open mathematical questions

1. Sharpen the rigorous enclosure of $\lambda_\infty$ and seek an analytic or algebraic characterization where possible.
2. Prove the all-level quadratic increment law and identify its coefficient.
3. Establish an unconditional source-to-source identification with the external $\theta=2\pi$ operator.
4. Characterize the complete exceptional set in the graph's spectral-decimation correspondence.
5. Obtain robust finite-level spectral-exponent estimates with controlled corner corrections.
6. Prove the observed signed-$Z_2$ H10 recurrence uniformly in the level.

## Test and reproducibility guide

### Requirements

- Python 3.10 or later
- NumPy
- SciPy
- pytest for tests

### Install

From a clone of this repository:

~~~bash
python -m venv .venv
source .venv/bin/activate       # macOS / Linux
python -m pip install --upgrade pip
python -m pip install -e .
python -m pip install pytest
~~~

A minimal import check:

~~~bash
python -c "import phi_genesis; print('Phi-Genesis import OK')"
~~~

### Run the normal test suite

~~~bash
pytest -q -m "not nightly"
~~~

Nightly tests are marked separately because they can involve deeper spectra, larger memory use, or Monte Carlo sweeps. To run all tests, including nightly diagnostics:

~~~bash
pytest -q
~~~

Use the workflow logs to distinguish a completed pass from a still-running job:

- [GitHub Actions — all workflows](https://github.com/RFT-SIRM/Phi-Genesis/actions)
- [Tests workflow](https://github.com/RFT-SIRM/Phi-Genesis/actions/workflows/tests.yml)
- [Nightly deep tests](https://github.com/RFT-SIRM/Phi-Genesis/actions/workflows/nightly-deep-tests.yml)

### Reproduce the Schur spectral-limit work

From the repository root, run the Lean formalization and the high-precision finite-level calculation:

~~~bash
lake build PhiGenesis
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/schur_bottom_eigenvalue.py
~~~

The Lean target checks the formal theorem. The Python script computes finite-level values and diagnostics; it does not certify the infinite-level limit. See the [proof map](computational/spectral_gap_theta_2pi/PROOF_MAP.md) and [high-precision note](computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md).

### Reproduce the finite-level estimator studies

~~~bash
python protocol_data/op2_window_bias.py table
python protocol_data/op2_window_bias.py sliding
python protocol_data/op2_chord_estimator.py 8 9
~~~

These computations use the committed cached count data and/or perform numerical sparse-LU inertia counts. Resource use depends on level and environment; level 10 has been reported at roughly 700 MB for a count. Higher levels have not been asserted to work within a fixed memory budget.

### Reproducibility checklist

- [ ] Record the commit SHA, Python version, dependency versions, and operating system.
- [ ] Preserve the preregistration and null pools used by the run.
- [ ] Distinguish fast CI from nightly/deep tests.
- [ ] Report the full configuration family and null comparison, not only the best match.
- [ ] Keep residual means, medians, maxima, and thresholds distinct.
- [ ] Do not replace an unresolved discrepancy with a badge, fit statistic, or unqualified success statement.

---

## How this connects to the wider RFT-SIRM programme

Phi-Genesis is part of a family of related research repositories. Their topics are connected by broad questions about recursive structures, invariants, and reproducible evidence, but **their mathematical objects and evidence status are not interchangeable**.

| Programme | What it studies | What must not be inferred |
|---|---|---|
| [**Evgeny-Theorem**](https://github.com/RFT-SIRM/Evgeny-Theorem) | A specified SU(2)-connected Sierpiński-gasket operator and a fourth-moment trace-defect identity; the source repository reports a Lean 4 formalization for its stated concrete operators. | Its formal proof does not transfer to Phi-Genesis's signed Z₂-flux Laplacian or its mass-index conjecture. |
| [**Evgeny's Theory of Everything**](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything) | A broader research programme and dissertation covering recursive operators, trace defects, finite-level higher-moment certificates, numerical holdouts, and open recurrence questions. | The title describes the programme's scope; it is not a claim that a complete physical Theory of Everything has been established. Finite-level evidence does not automatically prove an all-level recurrence. |
| [**UltraCore-RFT**](https://github.com/RFT-SIRM/UltraCore-RFT) | A research and engineering hub for invariant systems, deterministic execution, mathematical foundations, and runtime architecture, with an evidence ledger across workstreams. | An engineering result, stress test, or application prototype is not automatically a mathematical theorem or independent validation of Phi-Genesis. |

### Mathematical relationship: explicit, not assumed

The fourth-moment theorem and Phi-Genesis investigate different operators and observables. The former concerns a specified non-Abelian SU(2) connection and a trace defect; Phi-Genesis studies the Schur recursion, limiting least eigenvalue, and separate signed-graph computational workstreams. A rigorous bridge between these constructions has **not** been established in this repository.

The dissertation is useful context and a source of related mathematical questions, not a shortcut around Phi-Genesis's own unresolved tests.

- [Complete dissertation](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)
- [Fourth-moment theorem statement](https://github.com/RFT-SIRM/Evgeny-Theorem/blob/main/THEOREM.md)
- [Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/tree/main/formalization)
- [UltraCore-RFT research hub](https://github.com/RFT-SIRM/UltraCore-RFT)

---

## Authorship and correspondence

**Evgeniy Zaprudnov**  
*Research author · RFT-SIRM*

For research correspondence, use [evgeniyzaprudnov@gmail.com](mailto:evgeniyzaprudnov@gmail.com?subject=Phi-Genesis%20research%20enquiry). For machine-readable citation and author metadata, see [`CITATION.cff`](CITATION.cff).

---

## Research standards and citation

This repository aims to make the computational record auditable:

1. **State the operator and conventions.** Boundary degrees, graph level, signed edges, and the definition of the counted spectrum matter.
2. **Keep methods and results together.** Link every important number to code, a test, protocol, or data artifact.
3. **Preserve negative results.** Failed searches and uninformative tests are part of the record.
4. **Control selection effects.** Count all configurations tried and use null ensembles and power checks defined before evaluation.
5. **Distinguish evidence types.** Passing a test supports only the assertions that test actually executes.
6. **Do not silently promote claims.** A fit is not a prediction; a finite computation is not an all-level proof; related projects are not automatically equivalent.

If you use this code or cite the reported numerical results, cite the repository and identify the commit, environment, and relevant protocol/data version. Keep supplementary physical applications separate from the mathematical proof chain and state their own evidence boundaries.

- [Repository](https://github.com/RFT-SIRM/Phi-Genesis)
- [Citation and author metadata](CITATION.cff)
- [Commit history](https://github.com/RFT-SIRM/Phi-Genesis/commits/main/)
- [Research history timeline](https://rft-sirm.github.io/Phi-Genesis/history.html)
- [Issue tracker](https://github.com/RFT-SIRM/Phi-Genesis/issues)
- [Project files and declared reuse terms](https://github.com/RFT-SIRM/Phi-Genesis) — check the repository's actual license metadata before reusing code or text.

## Repository map

The repository is organized as a connected research record: formal proofs, exact computational audits, numerical experiments, preregistered statistical tests, and the documentation history are kept in distinct, traceable locations. The tree below reflects the files and directories present on the official `main` branch.

### Complete repository tree

```text
.
├── .github/
│   └── workflows/
│       ├── docs.yml
│       ├── ecosystem-control.yml
│       ├── lean.yml
│       ├── nightly-deep-tests.yml
│       ├── pages.yml
│       ├── spectral-gap-theta2pi.yml
│       └── tests.yml
├── .gitignore
├── CHANGELOG.md
├── CITATION.cff
├── METHODOLOGY.md
├── PREREGISTRATION.md
├── PREREGISTRATION_v1.1_DRAFT.md
├── PREREGISTRATION_v1.2_DRAFT.md
├── PREREGISTRATION_v1.2.1.md
├── PhiGenesis.lean
├── PhiGenesis/
│   ├── H10/
│   │   ├── BoundaryRowTransform.lean
│   │   ├── GasketCoordinates.lean
│   │   ├── GasketVertexChildCells.lean
│   │   ├── GasketVertexExplicit.lean
│   │   ├── GasketVertexGeometry.lean
│   │   ├── GasketVertexMem.lean
│   │   ├── GasketVertexOrder.lean
│   │   ├── GasketVertexSplit.lean
│   │   ├── GasketVertexStateA.lean
│   │   ├── IncidenceForest.lean
│   │   ├── Smoke.lean
│   │   └── VertexOrder.lean
│   └── SpectralGap/
│       ├── FiniteFaceCover.lean
│       ├── GlobalFaceEnergy.lean
│       ├── RecursiveSierpinskiFaces.lean
│       ├── SignedGaugeEnergy.lean
│       ├── SignedLaplacianMatrix.lean
│       └── TriangleEnergy.lean
├── README.md
├── computational/
│   ├── higher_moments_z2/
│   │   ├── FOLLOWUP_2026-11-03.md
│   │   ├── GF2_PIVOT_RECURSION_2026-11-04.md
│   │   ├── H10_ALL_LEVEL_CHECKPOINT_2026-11-04.md
│   │   ├── LEAN4_FORMALIZATION_TASK_2026-11-04.md
│   │   ├── Q_truth_table_16.csv
│   │   ├── README.md
│   │   ├── audit_gf2_pivot_tree.py
│   │   ├── edge2_alternative_residuals_transitions_4_7.csv
│   │   ├── followup_summary.json
│   │   └── full_flux_h10_levels_1_10.csv
│   └── spectral_gap_theta_2pi/
│       ├── RESEARCH_LOG_2026-11-05.md
│       └── audit_triangle_gauge.py
├── docs/
│   ├── application-programmes.md
│   ├── architecture.md
│   ├── changelog.md
│   ├── computational-architecture.md
│   ├── data-and-provenance.md
│   ├── dissertation.md
│   ├── ecosystem-control.md
│   ├── field_trials.md
│   ├── field_trials_sel4.md
│   ├── foundations.md
│   ├── glossary.md
│   ├── higher-moments-z2.md
│   ├── history.html
│   ├── history.md
│   ├── implementation.md
│   ├── index.md
│   ├── interactive.md
│   ├── interactive/
│   │   └── index.html
│   ├── legacy-landing.html
│   ├── methodology.md
│   ├── open-problems.md
│   ├── origin-chronology.md
│   ├── platform.md
│   ├── preregistration.md
│   ├── protocol-ledger.md
│   ├── reproducibility.md
│   ├── research-home.md
│   ├── research-map.md
│   ├── selection-protocol.md
│   ├── strategy.md
│   ├── stylesheets/
│   │   └── phi-genesis.css
│   ├── support.md
│   └── verified-results.md
├── lake-manifest.json
├── lakefile.lean
├── lean-toolchain
├── mkdocs.yml
├── phi_genesis/
│   ├── __init__.py
│   ├── decimation_check.py
│   ├── dirac_eta.py
│   ├── fukushima_shima.py
│   ├── higher_moments_z2.py
│   ├── mass_check.py
│   ├── mobius.py
│   ├── mobius_selection_search.py
│   ├── selection_protocol.py
│   ├── selection_protocol_v11.py
│   ├── selection_protocol_v121.py
│   ├── sg_index_triviality.py
│   ├── sg_inertia.py
│   ├── sg_laplacian.py
│   ├── sierpinski_carpet.py
│   └── spectral_convergence.py
├── protocol_data/
│   ├── gen_rank_pool.py
│   ├── null_pools_v1.json
│   ├── null_pools_v1_1.json
│   ├── null_pools_v1_2_1.json
│   ├── op2_chord_estimator.py
│   ├── op2_chord_estimator.txt
│   ├── op2_counts.json
│   ├── op2_window_bias.py
│   ├── power_by_k.py
│   ├── power_by_k_design_v1_1.txt
│   ├── power_design_v1_2_1.py
│   ├── power_design_v1_2_1.txt
│   ├── results_v1.json
│   ├── results_v1_1.json
│   ├── results_v1_2_1.json
│   └── structure_check_exploratory.py
├── protocol_ledger.md
├── pyproject.toml
├── requirements.txt
├── scripts/
│   └── ecosystem_status.py
├── test_carpet_lookelsewhere.py
├── test_convergence_and_selection.py
├── test_decimation_gate_a.py
├── test_decimation_residual_summary.py
├── test_fukushima_shima.py
├── test_higher_moments_z2.py
├── test_honest.py
├── test_mobius.py
├── test_nightly_deep.py
├── test_selection_protocol.py
├── test_selection_protocol_v121.py
├── test_sg_index_triviality.py
├── test_sg_inertia.py
├── test_top_quark_consistency.py
└── visual/
    ├── index.html
    └── interactive/
        └── index.html
```

### Architecture at a glance

- **Lean 4 entry point and build.** `PhiGenesis.lean`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`. Define the formalization entry point, the dependencies and the reproducible Lean environment.
- **H10 / GF(2) formalization.** `PhiGenesis/H10/`. Boundary-row transforms, incidence forests, gasket coordinates, recursive vertex geometry and vertex ordering.
- **Signed spectral-gap formalization.** `PhiGenesis/SpectralGap/`. Finite-face covers, recursive gasket faces, signed Laplacians, gauge energy and triangle energy.
- **Exact H10 computational record.** `computational/higher_moments_z2/`, `phi_genesis/higher_moments_z2.py`. Finite-level exact calculations, pivot-tree audits, formalization checkpoints and the research ledger.
- **Spectral-gap computational record.** `computational/spectral_gap_theta_2pi/`. Research log and triangle-gauge audit for the signed spectral-gap line.
- **Numerical research package.** `phi_genesis/`. Gasket Laplacians, decimation checks, flux operators, inertia counts, moments and related numerical studies.
- **Statistical protocols and evidence.** `PREREGISTRATION*.md`, `protocol_data/`, `protocol_ledger.md`. Preregistered selection rules, null pools, power checks, recorded outcomes and the cumulative protocol history.
- **Regression and audit suite.** Root-level `test_*.py` files. Executable checks for numerical conventions, spectral behavior, flux experiments, statistical protocols and reported caveats.
- **Research documentation and history.** `docs/`, `CHANGELOG.md`, `METHODOLOGY.md`. Research map, foundations, methods, data provenance, open problems, verified results, chronology and documentation history.
- **Documentation and visual site.** `mkdocs.yml`, `.github/workflows/docs.yml`, `visual/`. Site configuration, publication workflow and visual assets.
- **Project automation.** `.github/workflows/`, `scripts/`. CI, Lean builds, tests, nightly diagnostics, documentation and ecosystem-status tooling.
- **Citation and package metadata.** `CITATION.cff`, `pyproject.toml`. Author attribution, research-group affiliation, contact email and software citation metadata.

### Recommended navigation

| Purpose | Start with |
|---|---|
| Research overview | [Research map](docs/research-map.md) · [Documentation home](docs/index.md) |
| Mathematical foundations and terminology | [Foundations](docs/foundations.md) · [Glossary](docs/glossary.md) |
| H10 recurrence and exact GF(2) work | [H10 research note](docs/higher-moments-z2.md) · [Computational record](computational/higher_moments_z2/README.md) |
| Lean formalization | `PhiGenesis.lean` · `PhiGenesis/H10/` · `PhiGenesis/SpectralGap/` |
| Reproduction and provenance | [Reproducibility guide](docs/reproducibility.md) · [Data and provenance](docs/data-and-provenance.md) |
| Research history | [History](docs/history.md) · [Origin chronology](docs/origin-chronology.md) · [Changelog](CHANGELOG.md) |
| Open questions | [Open problems](docs/open-problems.md) · [Verified results](docs/verified-results.md) |

The repository keeps formal statements, finite computational certificates, numerical observations, and unresolved questions separate. A file's presence in the tree is not itself evidence that the claim it concerns has been proved; use the linked research notes, logs, tests, and CI records to determine the status of each result.

---

<p align="center">

**Evidence first. Reproducibility always. Open problems stay open until they are resolved.**

</p>
