# Phi-Genesis — Spectral Research Home

**Sierpiński-gasket spectral structure, boundary-condition experiments, reproducible computation, and evidence-bounded research.**

> 🟢 **FEATURED RESEARCH RECORD**
>
> **Spectral decimation, corner-defect corrections, and the target-index selection audit**
>
> Phi-Genesis separates numerically reproduced spectral structure, finite-level estimates, preregistered tests, and open conjectures. The research record does **not** establish an independent spectral rule selecting the target indices \(\{1,12,17,40\}\), and it does not claim a completed physical mass-generation mechanism.

Phi-Genesis is the RFT-SIRM spectral research programme for the Sierpiński gasket. Begin with the research map and the boundaries of the available evidence; then inspect the results, selection protocol, computational methods, and chronology. The versioned source records remain authoritative.

- [**Research map — follow the evidence**](research-map.md)
- [Verified spectral results and limitations](verified-results.md)
- [Selection protocol and negative results](selection-protocol.md)
- [Interactive spectral research portal](interactive/index.html)
- [Research history and chronology](history.html)
- [Project README and source repository](https://github.com/RFT-SIRM/Phi-Genesis)

> **Scope:** Phi-Genesis is a numerical spectral audit. Its findings do not inherit the Lean proof status of the separate Evgeny-Theorem repository. A reproduced finite-level observation, a statistical test, a fitted relation, and a mathematical theorem are different evidence classes.

## Research map

Use the [Research Map](research-map.md) to navigate the research hierarchy, spectral anchor, evidence labels, and unresolved questions. The map is organized by research relationship and evidence status, not by an implied claim that every downstream hypothesis follows from the spectral observations.

## The mathematical anchor

For the Sierpiński gasket, the theoretical spectral exponent is

\[
\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx 0.6826.
\]

The factor-five spectral-decimation structure and Fukushima–Shima gap structure are reproduced numerically within the documented finite-level scope, with corner-defect corrections for the corner-degree-2 graph Laplacian. Finite-window estimates remain sensitive to the counting window and estimator; the known exponent is a consistency reference, not a new prediction.

The proposed mass relation

\[
m=A n
\]

uses a fitted scale and the target indices \(\{1,12,17,40\}\). Those indices have **not** been independently derived from a spectral invariant. The relation is a fit, not a prediction.

## Research strands

| Strand | Primary page | Current status |
|---|---|---|
| Spectral decimation and gap structure | [Verified Results](verified-results.md) | Numerically reproduced within the documented scope; corner corrections matter |
| Spectral counting and spectral dimension | [Open Problems](open-problems.md) | Finite-level exponent estimates remain window-sensitive |
| Möbius / \(\pi\)-flux boundary conditions | [Verified Results](verified-results.md) | Tested configurations open a gap; target selection is not established |
| Target-index selection \(\{1,12,17,40\}\) | [Selection Protocol](selection-protocol.md) | Preregistered tests did not meet the decision threshold |
| Reproducibility and search provenance | [Data & Provenance](data-and-provenance.md) | Versioned records and code are the source of truth |
| Interactive exploration and chronology | [Interactive Portal](interactive.md) · [History](history.html) | Separate from the main documentation |

## Documentation

| Document | Purpose |
|---|---|
| [Research Map](research-map.md) | Research hierarchy, evidence classes, and reading order |
| [Verified Results](verified-results.md) | Numerical observations, measurements, and explicit limitations |
| [Selection Protocol](selection-protocol.md) | Preregistered search families, thresholds, and negative results |
| [Open Problems](open-problems.md) | Unresolved questions and requirements for further work |
| [Methodology](methodology.md) | Statistical design, power checks, and look-elsewhere correction |
| [Reproducibility](reproducibility.md) | Environment, commands, and reproduction entry points |
| [Computational Architecture](computational-architecture.md) | Computational modules, tests, and data artifacts |
| [Data & Provenance](data-and-provenance.md) | Source-of-truth hierarchy and cumulative search record |
| [Protocol Ledger](protocol-ledger.md) | Recorded evaluations and limitations of the historical search record |
| [Preregistration](preregistration.md) | Binding protocol versions and decision rules |
| [Changelog](changelog.md) | Version history and material changes |
| [Glossary](glossary.md) | Terms used throughout the spectral audit |
| [Support](support.md) | Research correspondence and reproducibility feedback |

## Selected results and limits

- **Spectral decimation:** eigenvalues scale by approximately a factor of five between levels, subject to the documented corner-defect correction.
- **Weyl exponent:** \(d_s/2=\ln 3/\ln 5\) is the theoretical value; finite-window estimates show phase-dependent spread.
- **Boundary twists:** the tested full \(\pi\)-flux configuration opens a spectral gap, but this does not select all four target indices.
- **Selection audit:** preregistered tests v1.0, v1.1, and v1.2.1 did not meet the required threshold. Version v1.0 was underpowered; v1.1 and v1.2.1 could reach the threshold but did not.
- **\(\eta\)-invariant:** the previously claimed value \(-4\) was not reproduced in the documented tests.
- **Top-quark index:** candidates 1654, 1664, and 1680 remain inconsistent under the documented scale choices; no candidate is asserted as correct.

These are bounded findings about tested operators, configurations, methods, and parameter ranges. They do not establish a physical mass-generation mechanism.

## Primary research records

The versioned source records supersede summaries on this site:

- [Project README and final status](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md)
- [Methodology source](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md)
- [Source code and tests](https://github.com/RFT-SIRM/Phi-Genesis)

## Research ecosystem

Phi-Genesis is a distinct spectral-computation workstream within [RFT-SIRM](https://github.com/RFT-SIRM). Its interactive portal and research history remain separate destinations; neither replaces the main documentation or the primary records.

[![Docs CI](https://github.com/RFT-SIRM/Phi-Genesis/actions/workflows/pages.yml/badge.svg)](https://github.com/RFT-SIRM/Phi-Genesis/actions)

_Copyright 2026 Evgeniy Zaprudnov (RFT-SIRM)._
