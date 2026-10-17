# Phi-Genesis — Spectral Research on the Sierpiński Gasket

[![Research programme](https://img.shields.io/badge/RFT--SIRM-Phi--Genesis-5b4bc4?style=for-the-badge)](https://github.com/RFT-SIRM/Phi-Genesis)
[![Python](https://img.shields.io/badge/Python-3.10%2B-3776AB?style=for-the-badge&logo=python&logoColor=white)](https://www.python.org/)
[![Tests](https://img.shields.io/badge/Tests-Pytest-168f83?style=for-the-badge&logo=pytest&logoColor=white)](https://github.com/RFT-SIRM/Phi-Genesis/actions)
[![Interactive portal](https://img.shields.io/badge/Explore-Interactive%20Portal-087ea4?style=for-the-badge)](https://rft-sirm.github.io/Phi-Genesis/interactive/)
[![Research history](https://img.shields.io/badge/Read-Research%20History-0f766e?style=for-the-badge)](https://rft-sirm.github.io/Phi-Genesis/history.html)

**Phi-Genesis is a reproducible computational research project** studying spectral properties of graph Laplacians on the Sierpiński gasket, signed \(\mathbb{Z}_2\)-flux / \(\pi\)-flux boundary conditions, spectral decimation, and a proposed integer-index fermion-mass pattern. It keeps positive results, negative results, unresolved discrepancies, and the limits of each method visible.

> [!IMPORTANT]
> **Scientific status, not marketing status:** spectral and gap observations are numerical results scoped to the implemented operators and tested levels. The proposed mass-index selection rule \(\{1,12,17,40\}\) has **not** been established. The formula \(m=A n\) is a numerical fit, not a prediction, until an independent rule derives the indices without looking at the masses. Gate A—the full characterization of spectral-decimation exceptions for the implemented corner-degree-2 Laplacian—also remains open.

<div align="center">

[**Open the interactive research portal →**](https://rft-sirm.github.io/Phi-Genesis/interactive/) · [**Browse the research map →**](https://rft-sirm.github.io/Phi-Genesis/research-map.html) · [**Read the dissertation →**](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)

</div>

---

## Contents

- [At a glance](#at-a-glance)
- [Evidence dashboard](#evidence-dashboard)
- [Mathematical core](#mathematical-core)
- [Key numerical results](#key-numerical-results)
- [Mass-index audit](#mass-index-audit)
- [Preregistered selection tests](#preregistered-selection-tests)
- [Open problems and Gate A](#open-problems-and-gate-a)
- [Test and reproducibility guide](#test-and-reproducibility-guide)
- [Repository map](#repository-map)
- [How this connects to the wider RFT-SIRM programme](#how-this-connects-to-the-wider-rft-sirm-programme)
- [Research standards and citation](#research-standards-and-citation)

## At a glance

| Research question | Current answer | Evidence label |
|---|---|---|
| Does the Sierpiński-gasket spectrum show the expected decimation and gap structure? | Reproduced numerically on finite graph levels, with explicit corner-defect qualifications. | **NUMERICALLY REPRODUCED** |
| Can the spectral dimension be recovered from finite-level counts? | The theoretical exponent is \(d_s/2=\ln 3/\ln 5\). A theory-motivated chord estimator approaches \(\ln 3/\ln(5-\sigma)\) to better than 0.1% on the reported level-9 subset with \(N\ge1000\). | **NUMERICAL CONSISTENCY CHECK** |
| Does a \(\pi\)-flux boundary condition open a gap? | The tested full \(\pi\)-flux case opens a gap; the first level-5 eigenvalue changes from approximately 0.006 to 0.46. | **NUMERICALLY REPRODUCED** |
| Has a spectral rule independently selected \(\{1,12,17,40\}\)? | No. Preregistered families did not produce evidence above the specified null thresholds. | **NOT ESTABLISHED** |
| Is \(m=A n\) a predictive mass law? | Not at present: the four integer indices were chosen with the target masses in view, and no independent selection mechanism has been derived. | **FIT, NOT PREDICTION** |
| Is Gate A closed? | No. Matched eigenvalue pairs can be at machine precision, but the full recursively generated exceptional set and complete correspondence are not yet characterized. | **OPEN** |
| Does the project reproduce the reported \(\eta\)-invariant value \(-4\)? | No. The tested potential gives asymmetry \(+1\); \(-4\) was not observed in the reported checks. | **NOT REPRODUCED** |

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

<details>
<summary><strong>Established numerically: spectral structure and boundary experiments</strong></summary>

- **Spectral decimation:** the polynomial map \(\phi(\lambda)=\lambda(5-\lambda)\) describes the expected structure, but for the implemented graph Laplacian with degree-2 corners the correspondence includes boundary/corner-defect corrections. Gate A is deliberately not marked closed.
- **Fukushima–Shima gap structure:** forbidden spectral zones cluster around the documented decimation fixed-point region, including \(\lambda\approx2.5\) and \(\lambda\approx3\).
- **Log-periodicity:** the spectrum exhibits the scale signature associated with factor-5 decimation, with period \(\ln 5\) in the log-spectral variable.
- **Weyl exponent:** the theoretical exponent is \(\ln3/\ln5\approx0.6826\). Finite-level regression estimates depend on the selected window; the chord-estimator result is a separate, theory-motivated numerical consistency check.
- **Full \(\pi\)-flux:** the tested level-5 first eigenvalue changes from about 0.006 to about 0.46, consistent with a gap opening in that setup.
- **Exhaustive generation-twist search:** all \(2^5=32\) level-5 configurations were checked. No configuration selected more than one of the four target indices; index 40 was not selected.

These are scoped to the operators, graph conventions, levels, and numerical procedures actually used. They are not a proof of a mass-index law.

</details>

<details>
<summary><strong>Negative results and caveats that must remain visible</strong></summary>

- The three documented preregistered selection protocols did not establish a selection rule for \(\{1,12,17,40\}\).
- The earliest protocol, v1.0, could not reach its target significance threshold even under its best possible hit pattern. Its negative result is therefore **uninformative**. Later v1.1 and v1.2.1 protocols passed the null-only power check and still did not reach the threshold.
- The earlier Sierpiński-carpet search produced an apparent four-index match, later identified as vulnerable to a look-elsewhere effect. It is retained in the research history rather than promoted as supporting evidence.
- Index 1 is selected by the ratio-based gap rule very frequently under random on-site potentials (about 95% in the reported audit); index 40 appears much less often (about 3.4%). These hits do not carry equal evidential weight.
- The top-quark index remains inconsistent across the historical estimate, the current scale formula, and the best integer fit: 1680, 1664, and 1654 respectively.
- The reported \(\eta\)-invariant value \(-4\) was not reproduced for the specified potential.
- Gate A is not closed merely because a subset of predicted/observed eigenvalue pairs match to machine precision.

</details>

## Mathematical core

### 1. Sierpiński-gasket spectral decimation

The working decimation map is

\[
\boxed{\phi(\lambda)=\lambda(5-\lambda)}
\]

For the idealized decimation relation, inverse branches are used to compare candidate preimages across graph levels. In the actual implementation, the graph Laplacian has degree-2 corner vertices, and this boundary convention produces exceptional pairs and residuals that must be characterized rather than hidden.

**Gate A status:** some pairs match to floating-point machine precision; the simple exclusion of exceptional values \(\{2,5,6\}\) does not account for every mismatch. The nightly diagnostic checks that the machine-exact subset really is exact at numerical precision and that its match rate increases across levels 5–7. This is evidence about the checked pairs and trend—not proof that the full decimation correspondence is closed.

- [Gate A diagnostic test](test_decimation_gate_a.py)
- [Residual-statistics tests](test_decimation_residual_summary.py)
- [Spectral decimation implementation](phi_genesis/sg_laplacian.py)
- [Fukushima–Shima checks](test_fukushima_shima.py)

### 2. Spectral dimension and the Weyl exponent

For the Sierpiński gasket, the theoretical exponent is

\[
\boxed{\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx0.682606}
\]

The counting function \(N(\lambda)\) counts eigenvalues below a threshold \(\lambda\), with the precise convention defined by the implementation. Finite-level regressions are sensitive to the fitting window because the counting staircase has log-periodic structure.

The exploratory chord estimator compares a count at \(\sigma\) with a count at its decimation image \(\phi(\sigma)\):

\[
\widehat{d_s/2}(\sigma)=
\frac{\ln\!\left[N(\phi(\sigma))/N(\sigma)\right]}
{\ln\!\left[\phi(\sigma)/\sigma\right]}
\]

Under the working count relation, this tends toward

\[
\frac{\ln 3}{\ln(5-\sigma)}
\longrightarrow
\frac{\ln 3}{\ln 5}
\qquad (\sigma\to0)
\]

**Reported numerical result:** at level 9, for the 14 sampled points with \(N\ge1000\), the chord estimate differs from \(\ln3/\ln(5-\sigma)\) by an average of about \(-0.03\%\), with a range of approximately \(-0.08\%\) to \(+0.07\%\). This is an exploratory consistency check added after the regression study—not a preregistered discovery and not new physical evidence. The exact theoretical exponent itself is not in question; the open problem is stable finite-level estimation and full control of the corner correction.

- [Inertia counting implementation](phi_genesis/sg_inertia.py)
- [Window-bias experiment](protocol_data/op2_window_bias.py)
- [Chord-estimator experiment](protocol_data/op2_chord_estimator.py)
- [Open Problem #2 data and discussion](protocol_data/)

### 3. Boundary conditions and \(\pi\)-flux

The project studies signed graph operators representing \(\mathbb{Z}_2\)-flux / Möbius-style boundary twists. The reported level-5 full-\(\pi\)-flux calculation changes the first eigenvalue from approximately 0.006 to 0.46. Partial twists were also tested.

This establishes a gap in the tested numerical setup; it does **not** establish that the target fermion indices are selected by the gap. The exhaustive 32-configuration generation-twist search reached at most one of the four target indices, and index 40 was never selected.

- [Signed-flux operator](phi_genesis/mobius.py)
- [Exhaustive twist search](phi_genesis/mobius_selection_search.py)
- [Twist tests](test_mobius.py)

---

## Key numerical results

### Spectral estimates

| Quantity | Reported value | Interpretation |
|---|---:|---|
| Theoretical \(d_s/2\) | \(\ln3/\ln5\approx0.6826\) | Theoretical reference exponent |
| Naive regression, level 6 | 0.7051 | About 3.3% above reference |
| Naive regression, level 8 | 0.7019 | About 2.8% above reference |
| Level-9 chord estimate, \(N\ge1000\) | Within 0.1% of \(\ln3/\ln(5-\sigma)\) | 14 sampled points; exploratory consistency check |
| Full \(\pi\)-flux first eigenvalue, level 5 | About 0.46 | Compared with about 0.006 in the untwisted case |
| Claimed \(\eta\)-asymmetry, specified potential | +1 | The advertised value \(-4\) was not reproduced |

### What the scale audit says

The current four-fermion integer fit uses \(A=104.63\,\text{MeV}\). A separate expression \(A=v\alpha/\Phi^6\) gives about 100.13 MeV, approximately 4.3% lower. The discrepancy is documented, not reconciled.

| Scale or statistic | Value | Status |
|---|---:|---|
| Integer-fit scale \(A\) | 104.63 MeV | Fitted to the four selected masses |
| Formula-derived scale \(v\alpha/\Phi^6\) | 100.13 MeV | 4.3% below fitted value |
| Relative spread of implied per-fermion scales | 0.58% | Descriptive fit statistic |
| Mean error for four selected integer indices | 0.68% | In-sample agreement; not predictive validation |
| Earlier fitted-decimal mean error | 0.87% | Different fit, not an independent test |

---

## Mass-index audit

The explored formula is

\[
\boxed{m=A\,n}
\]

where \(A\) is a common scale and \(n\) is an integer index. The table below reports the project's current integer fit for four heavy fermions.

| Fermion | Index \(n\) | Predicted mass (MeV) | Comparison mass (MeV) | Relative error |
|---|---:|---:|---:|---:|
| Muon (\(\mu\)) | 1 | 104.63 | 105.658 | 0.97% |
| Tau (\(\tau\)) | 17 | 1778.71 | 1776.86 | 0.10% |
| Charm (\(c\)) | 12 | 1255.56 | 1275.00 | 1.52% |
| Bottom (\(b\)) | 40 | 4185.20 | 4180.00 | 0.12% |
| **Mean** | — | — | — | **0.68%** |

> [!WARNING]
> The small mean error is not independent evidence for the index pattern. Four integers were selected with the four masses in view, then one scale was fitted. Without a rule that selects \(n\) independently of those masses, the result remains a numerical match, not a prediction.

### Top-quark consistency: unresolved

| Candidate | \(n_t\) | Origin |
|---|---:|---|
| Historical advertised value | 1680 | Derived using an older scale of approximately 103.63 MeV |
| Current formula-based candidate | 1664 | \(v/(\sqrt2 A)\) using \(A=104.63\) MeV |
| Current best integer fit | 1654 | \(\operatorname{round}(m_t/A)\) using \(A=104.63\) MeV |

The three candidates are not interchangeable. With the current scale, using 1680 gives a top-quark error of about 1.55%, more than twice the four-fermion mean error. No single top index is asserted as correct.

The index-1 triviality audit is another important caveat: under random on-site potentials, the ratio-based selection rule selects index 1 about 95% of the time, compared with about 37% for index 12, 22% for index 17, and 3.4% for index 40 in the reported experiment. A hit on index 1 is therefore much weaker evidence for a mechanism than a hit on a rare index.

- [Mass-scale audit](phi_genesis/mass_check.py)
- [Top-quark consistency tests](test_top_quark_consistency.py)
- [Index-1 base-rate audit](test_sg_index_triviality.py)

---

## Preregistered selection tests

The central statistical question is not whether a configuration can be found that matches the target set after enough experimentation. It is whether a predeclared operator family selects \(\{1,12,17,40\}\) more often than chance after accounting for all configurations searched—the **look-elsewhere effect**.

| Protocol | Search rule | Configurations | Result | Power-check interpretation |
|---|---|---:|---|---|
| v1.0 | \(k=12\), window 60 | 75 | \(p=0.922\) and \(0.968\) in the two null ensembles | **Uninformative negative:** even the best hit pattern could not reach the threshold |
| v1.1 | \(k=6\), window 60 | 75 | \(p=0.966\) and \(0.997\) | **Informative negative:** threshold was reachable; at most 2/4 targets selected, index 40 selected by none |
| v1.2.1 | \(k=8\), window 60; continuum-circle/spin-structure family | 10 | \(p=0.953\) and \(0.926\) | **Informative negative:** threshold was reachable; at most 1/4 target selected |

Across the three protocols, the ledger records 193 configuration evaluations, plus the earlier carpet search (about 128 level-3 configurations and an unrecorded level-4 sweep). The combined count is therefore a **lower bound of about 321**, not an exact exhaustive count of every historical exploratory attempt.

The carpet's early apparent 4/4 match was subsequently reassessed using null controls and the look-elsewhere effect. The record keeps that episode visible so that it cannot later be cited as clean confirmation.

### Protocol rules

1. State the target indices, selection statistic, null ensembles, seeds, and significance threshold before evaluation.
2. Check statistical power using the null distribution alone. If the threshold cannot be reached, a negative result is uninformative.
3. Use the maximum score across all configurations in a family, rather than reporting only the best-looking configuration.
4. Account for the base rate of each target index; common hits and rare hits do not have equal evidential weight.
5. Keep abandoned branches and exploratory attempts in the ledger, and label post-hoc analyses explicitly.

**Current conclusion:** the tested families did not establish a spectral rule. This does not prove that no such rule exists; it means the tested rules failed to provide the required evidence.

- [Protocol overview](PREREGISTRATION.md)
- [v1.1 draft / record](PREREGISTRATION_v1.1_DRAFT.md)
- [v1.2 draft / record](PREREGISTRATION_v1.2_DRAFT.md)
- [v1.2.1 protocol](PREREGISTRATION_v1.2.1.md)
- [Complete protocol ledger](protocol_ledger.md)
- [Null pools, outputs, and seeds](protocol_data/)
- [Methodology: a worked negative example](METHODOLOGY.md)
- [Selection test code](phi_genesis/)

---

## Open problems and Gate A

<details open>
<summary><strong>Open Problem 1 — derive the mass indices independently</strong></summary>

**Question.** Can an operator invariant, boundary condition, or independently motivated construction select \(n\in\{1,12,17,40\}\) before the masses are compared?

**Tried:** generation-wise \(\mathbb{Z}_2\) twists, scalar vertex potentials, Dirichlet corner conditions, SG \(\times S^1\) with lattice and continuum-circle variants, and the earlier Sierpiński-carpet search. The preregistered protocols did not establish the target rule.

**Required next step:** a genuinely motivated new operator family or an analytical derivation of the indices, committed under a new preregistered protocol with a null-only power check. Repeating the same searches against the same targets would increase the look-elsewhere correction, not the evidence.

</details>

<details>
<summary><strong>Open Problem 2 — finite-level estimation of the spectral exponent</strong></summary>

Naive regression and sliding-window estimates vary with the log-spectral window. The level-9 chord estimator improves agreement on the reported high-count subset, but it is exploratory, has a finite sampled domain, and depends on the working decimation/count relation.

The exact theoretical exponent \(\ln3/\ln5\) is the reference. The open issue is a robust finite-level estimator with controlled corner corrections and a clearly stated domain—not a new determination of the theoretical exponent.

</details>

<details>
<summary><strong>Gate A — characterize the complete decimation exceptional set</strong></summary>

The map \(\phi(\lambda)=\lambda(5-\lambda)\) is correct for the matched pairs checked, and the largest reported residual among the machine-exact subset at levels 5–7 is approximately \(1.2\times10^{-14}\), \(2.0\times10^{-14}\), and \(5.2\times10^{-14}\), respectively.

That does **not** mean every expected preimage has a one-to-one match. A broader residual threshold can include near-misses; therefore the arithmetic mean over all broadly matched pairs must not be described as machine precision. The diagnostic explicitly separates:
- broad matches (residual below \(10^{-4}\));
- machine-exact matches (residual below \(10^{-10}\));
- near-misses that pass the broad threshold but not the machine-exact threshold.

The working explanation is that the full exceptional set is recursively generated and/or affected by the implemented corner boundary. Its complete structure remains uncharacterized. The nightly check guards the observed machine-precision subset and increasing-rate trend; it does not close Gate A.

</details>

<details>
<summary><strong>Open Problem 3 — light fermions and a physical bridge</strong></summary>

The electron, up, down, and strange fermions are not explained by the integer-index formula in its current form. A proposed fractal/NJL-style mechanism is not implemented as a fully specified predictive model here. Any additional coupling, cutoff, or other free parameter must be counted against the masses it is meant to explain.

The repository also does not define a Lagrangian and beta functions that derive the fitted scale \(A\) from the electroweak scale. Without those ingredients, a renormalization-group calculation cannot be used to claim that bridge has been established.

</details>

---

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

### Reproduce the v1.2.1 selection protocol

> [!CAUTION]
> The protocol's Step A rewrites the committed null-pool file. If you want to preserve the repository's checked-in output unchanged, run this on a clean disposable clone or back up the file first.

~~~bash
python -m phi_genesis.selection_protocol_v121 stepA
python -m phi_genesis.selection_protocol_v121 stepB
~~~

Compare the output with `protocol_data/results_v1_2_1.json` and the written protocol/ledger.

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

## Repository map

| Path | Purpose |
|---|---|
| `phi_genesis/sg_laplacian.py` | Sierpiński-gasket graph Laplacian, spectral tools, and decimation-related routines |
| `phi_genesis/mobius.py` | Signed \(\mathbb{Z}_2\)-flux / \(\pi\)-flux operator |
| `phi_genesis/mobius_selection_search.py` | Exhaustive generation-twist search |
| `phi_genesis/fukushima_shima.py` | Fukushima–Shima gap-structure analysis |
| `phi_genesis/sg_inertia.py` | Eigenvalue counting through Sylvester inertia and sparse factorization |
| `phi_genesis/spectral_convergence.py` | Dense spectra, Weyl fits, and window sensitivity |
| `phi_genesis/mass_check.py` | Mass-scale and consistency audit |
| `phi_genesis/dirac_eta.py` | Graph Dirac operator and \(\eta\)-invariant experiment |
| `test_decimation_gate_a.py` | Nightly Gate A diagnostic |
| `test_decimation_residual_summary.py` | Mean/median/threshold semantics and residual-statistics tests |
| `test_fukushima_shima.py` | Gap-structure checks |
| `test_mobius.py` | Flux/twist and integer-related tests |
| `test_sg_inertia.py` | Inertia-count checks and numerical cross-checks |
| `test_selection_protocol.py`, `test_selection_protocol_v121.py` | Preregistered selection-protocol checks |
| `test_sg_index_triviality.py` | Base-rate caveat for index 1 and other target indices |
| `test_top_quark_consistency.py` | Guards against silently mixing top-index candidates/scales |
| `protocol_data/` | Null pools, results, cached counts, and Open Problem #2 scripts |
| `PREREGISTRATION*.md`, `protocol_ledger.md` | Protocol specifications and cumulative search history |
| `METHODOLOGY.md` | Worked explanation of the look-elsewhere effect and negative results |
| `CHANGELOG.md` | Versioned project history |

For the documentation site, start at [the documentation home](https://rft-sirm.github.io/Phi-Genesis/), then use the [research map](https://rft-sirm.github.io/Phi-Genesis/research-map.html), [verified results](https://rft-sirm.github.io/Phi-Genesis/verified-results.html), [protocol ledger](https://rft-sirm.github.io/Phi-Genesis/protocol-ledger.html), [open problems](https://rft-sirm.github.io/Phi-Genesis/open-problems.html), or [research history](https://rft-sirm.github.io/Phi-Genesis/history.html).

---

## How this connects to the wider RFT-SIRM programme

Phi-Genesis is part of a family of related research repositories. Their topics are connected by broad questions about recursive structures, invariants, and reproducible evidence, but **their mathematical objects and evidence status are not interchangeable**.

| Programme | What it studies | What must not be inferred |
|---|---|---|
| [**Evgeny-Theorem**](https://github.com/RFT-SIRM/Evgeny-Theorem) | A specified SU(2)-connected Sierpiński-gasket operator and a fourth-moment trace-defect identity; the source repository reports a Lean 4 formalization for its stated concrete operators. | Its formal proof does not transfer to Phi-Genesis's signed \(\mathbb{Z}_2\)-flux Laplacian or its mass-index conjecture. |
| [**Evgeny's Theory of Everything**](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything) | A broader research programme and dissertation covering recursive operators, trace defects, finite-level higher-moment certificates, numerical holdouts, and open recurrence questions. | The title describes the programme's scope; it is not a claim that a complete physical Theory of Everything has been established. Finite-level evidence does not automatically prove an all-level recurrence. |
| [**UltraCore-RFT**](https://github.com/RFT-SIRM/UltraCore-RFT) | A research and engineering hub for invariant systems, deterministic execution, mathematical foundations, and runtime architecture, with an evidence ledger across workstreams. | An engineering result, stress test, or application prototype is not automatically a mathematical theorem or independent validation of Phi-Genesis. |

### Mathematical relationship: explicit, not assumed

The fourth-moment theorem and Phi-Genesis investigate different operators and observables. The former concerns a specified non-Abelian SU(2) connection and a trace defect; Phi-Genesis studies spectral properties of signed \(\mathbb{Z}_2\)-flux Laplacians and an exploratory mass-index pattern. A rigorous bridge between these constructions has **not** been established in this repository.

The dissertation is useful context and a source of related mathematical questions, not a shortcut around Phi-Genesis's own unresolved tests.

- [Complete dissertation](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)
- [Fourth-moment theorem statement](https://github.com/RFT-SIRM/Evgeny-Theorem/blob/main/THEOREM.md)
- [Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/tree/main/formalization)
- [UltraCore-RFT research hub](https://github.com/RFT-SIRM/UltraCore-RFT)

---

## Research standards and citation

This repository aims to make the computational record auditable:

1. **State the operator and conventions.** Boundary degrees, graph level, signed edges, and the definition of the counted spectrum matter.
2. **Keep methods and results together.** Link every important number to code, a test, protocol, or data artifact.
3. **Preserve negative results.** Failed searches and uninformative tests are part of the record.
4. **Control selection effects.** Count all configurations tried and use null ensembles and power checks defined before evaluation.
5. **Distinguish evidence types.** Passing a test supports only the assertions that test actually executes.
6. **Do not silently promote claims.** A fit is not a prediction; a finite computation is not an all-level proof; related projects are not automatically equivalent.

If you use this code or cite the reported numerical results, cite the repository and identify the commit, environment, and relevant protocol/data version. Acknowledge explicitly that the mass-index formula currently lacks an independent selection rule.

- [Repository](https://github.com/RFT-SIRM/Phi-Genesis)
- [Commit history](https://github.com/RFT-SIRM/Phi-Genesis/commits/main/)
- [Research history timeline](https://rft-sirm.github.io/Phi-Genesis/history.html)
- [Issue tracker](https://github.com/RFT-SIRM/Phi-Genesis/issues)
- [Project files and declared reuse terms](https://github.com/RFT-SIRM/Phi-Genesis) — check the repository's actual license metadata before reusing code or text.

---

<p align="center">

**Evidence first. Reproducibility always. Open problems stay open until they are resolved.**

</p>
