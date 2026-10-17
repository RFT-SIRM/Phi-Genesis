# Phi-Genesis — Spectral Research Laboratory

**Reproducible spectral computations, boundary-condition experiments, and an evidence-first audit of a proposed fermion mass-index rule.**

> **CURRENT RESEARCH STATUS · v2.2.1**
>
> Phi-Genesis reproduces selected spectral observations on the Sierpiński gasket, while keeping negative results and unresolved questions visible. The tested search families have **not** established an independent spectral selection rule for the target indices \(\{1,12,17,40\}\). Open Problem #2 remains open. Numerical results are not machine-checked theorems.

Phi-Genesis is the spectral-computation workstream of RFT-SIRM. Start with the research map, inspect the numerical evidence and preregistered selection audit, then use the separate interactive portal and the research history to explore the work. The versioned source records remain authoritative.

- [**Research map — start here**](research-map.md)
- [Verified results and evidence boundaries](verified-results.md)
- [Selection protocol and negative results](selection-protocol.md)
- [Interactive research portal](https://rft-sirm.github.io/Phi-Genesis/interactive/)
- [Research history](history.html)
- [Source repository and README](https://github.com/RFT-SIRM/Phi-Genesis)

## Research map

Use the [Research Map](research-map.md) to follow the main research strands and their evidence status. The site separates reproducible numerical observations, tested-but-unsuccessful selection rules, open methodological questions, and primary records.

## The mathematical anchor

For the Sierpiński gasket, the theoretical spectral exponent is

\[
\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx0.6826.
\]

The factor-5 spectral-decimation structure and Fukushima–Shima gap structure are reproduced numerically, with the documented corner-defect corrections for the corner-degree-2 graph Laplacian. The finite-level estimate of the exponent remains sensitive to the counting window and estimator; the known theoretical exponent is a consistency target, not a new prediction.

The proposed mass relation

\[
m=A n
\]

uses a fitted scale and the target indices \(\{1,12,17,40\}\). Those indices have **not** been independently derived from a spectral invariant. The relationship is therefore a numerical fit, not a prediction.

## Research strands

| Strand | Primary page | Current status |
|---|---|---|
| Spectral decimation and gap structure | [Verified Results](verified-results.md) | Numerically reproduced within stated finite-level scope |
| Spectral counting and spectral dimension | [Open Problem #2](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent) | Window sensitivity remains unresolved |
| Möbius / \(\pi\)-flux boundary conditions | [Verified Results](verified-results.md) | Tested cases open a gap; target selection is not established |
| Target-index selection \(\{1,12,17,40\}\) | [Selection Protocol](selection-protocol.md) | Preregistered tests did not meet the decision threshold |
| Reproducibility and search provenance | [Data & Provenance](data-and-provenance.md) | Versioned records and code are the source of truth |
| Interactive exploration and chronology | [Interactive Portal](https://rft-sirm.github.io/Phi-Genesis/interactive/) · [History](history.html) | Separate from the main documentation |

## Research documentation

| Document | Purpose |
|---|---|
| [Research Map](research-map.md) | Research hierarchy, evidence classes, and reading order |
| [Verified Results](verified-results.md) | Numerical observations, measurements, and explicit limitations |
| [Selection Protocol](selection-protocol.md) | Preregistered search families, null models, thresholds, and results |
| [Open Problems](open-problems.md) | Unresolved questions and conditions for further work |
| [Methodology](methodology.md) | Statistical design and look-elsewhere correction |
| [Reproducibility](reproducibility.md) | Reproduction instructions and test entry points |
| [Computational Architecture](computational-architecture.md) | Computational modules, tests, and data artifacts |
| [Data & Provenance](data-and-provenance.md) | Source-of-truth hierarchy and cumulative search record |
| [Protocol Ledger](protocol-ledger.md) | Counted evaluations and limits of the historical search record |
| [Preregistration](preregistration.md) | Binding protocol versions and decision rules |
| [Changelog](changelog.md) | Version history and material changes |
| [Glossary](glossary.md) | Terms used throughout the spectral audit |
| [Support](support.md) | Research correspondence and reproducibility feedback |

## Selected results and limits

- **Spectral decimation:** eigenvalues scale by approximately a factor of five between levels, subject to the documented corner-defect correction.
- **Weyl exponent:** \(d_s/2=\ln 3/\ln 5\) is the theoretical value; numerical finite-window estimates show phase-dependent spread.
- **Boundary twists:** the tested full \(\pi\)-flux configuration opens a spectral gap, but gap rules do not select all four target indices.
- **Selection audit:** preregistered tests v1.0, v1.1, and v1.2.1 found no evidence meeting the required threshold. The v1.0 test was underpowered; v1.1 and v1.2.1 could reach the threshold but did not.
- **\(\eta\)-invariant:** the previously claimed value \(-4\) was not reproduced in the documented tests.
- **Top-quark index:** candidates 1654, 1664, and 1680 remain inconsistent under the documented scale choices; no candidate is asserted as correct.

These are bounded findings about the tested operators, configurations, numerical methods, and parameter ranges. They do not establish a physical mass-generation mechanism.

## Primary research records

The source repository's versioned records supersede summaries on this site:

- [Project README and final status](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md)
- [Methodology source](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md)
- [Source code and tests](https://github.com/RFT-SIRM/Phi-Genesis)

## Scope and evidence discipline

The current evidence does **not** establish an operator invariant that independently selects \(\{1,12,17,40\}\). The fitted relation \(m=A n\) must not be described as a prediction. The cumulative search count is a lower bound because the earlier carpet branch included an unrecorded level-4 sweep. The finite-window exponent problem remains open.

Phi-Genesis is a numerical research project, not a Lean formalization of Evgeny's Theorem. Its results do not inherit the proof status of that separate repository.

## Research correspondence

For methodological criticism, collaboration proposals, or reproducibility feedback, use the [Phi-Genesis research contact route](mailto:evgeniyzaprudnov@gmail.com?subject=Phi-Genesis%20research%20enquiry).

---

_Copyright 2026 · RFT-SIRM · Phi-Genesis Spectral Research Laboratory._
