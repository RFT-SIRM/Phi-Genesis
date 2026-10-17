# Phi-Genesis — Spectral Research Laboratory

**Spectral decimation, graph spectra, boundary conditions, and reproducible numerical research on the Sierpiński gasket.**

> 🟢 **CURRENT RESEARCH STATUS · v2.2.1**
>
> Phi-Genesis records reproducible computations and bounded negative results. The tested search families have **not** established an independent spectral selection rule for the target indices \(\{1,12,17,40\}\). Open Problem #2 remains open. Numerical evidence is not presented as a machine-checked theorem.

Phi-Genesis is the RFT-SIRM spectral research programme. This site is its main documentation home: begin with the research map, inspect the mathematical and numerical evidence, follow the preregistered selection audit, and then explore the separate interactive portal.

- [**Open the Interactive Portal**](https://rft-sirm.github.io/Phi-Genesis/interactive/)
- [Research History](https://rft-sirm.github.io/Phi-Genesis/history.html)
- [Source repository](https://github.com/RFT-SIRM/Phi-Genesis)

## Research map

Use the [Research Map](research-map.md) to navigate the project’s main strands, current status and recommended reading order. It connects spectral decimation, spectral counting, boundary twists, target-index selection and reproducibility records.

## The mathematical anchor

For the Sierpiński gasket, the theoretical spectral exponent is

\[
\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx0.6826.
\]

The factor-5 decimation structure is documented with corner-defect corrections for the corner-degree-2 graph Laplacian used in this project. The Fukushima–Shima gaps are numerically reproduced in the documented finite-level checks. See [Verified Results](verified-results.md) for the exact scope and limitations.

## Research strands

| Strand | Primary page | Current status |
|---|---|---|
| Spectral decimation and gap structure | [Verified Results](verified-results.md) | Supported with stated corner-defect corrections |
| Spectral dimension and counting | [Open Problem #2](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent) | Finite-window sensitivity remains open |
| Möbius / π-flux boundary conditions | [Selection Protocol](selection-protocol.md) | Gap observed in tested cases; target selection not established |
| Selection of \(\{1,12,17,40\}\) | [Protocol Audit](selection-protocol.md) | Preregistered tests did not meet the decision threshold |
| Reproducibility and provenance | [Reproducibility](reproducibility.md) | Code, tests and versioned records remain primary |

## Documentation

| Document | Purpose |
|---|---|
| [Research Map](research-map.md) | Research hierarchy, status and reading order |
| [Verified Results](verified-results.md) | Numerical observations, fits and evidence boundaries |
| [Selection Protocol](selection-protocol.md) | Preregistered families, null models, power checks and results |
| [Open Problems](open-problems.md) | Unresolved questions and criteria for future work |
| [Methodology](methodology.md) | Statistical design and look-elsewhere correction |
| [Reproducibility](reproducibility.md) | Test commands and fixed-seed computation instructions |
| [Computational Architecture](computational-architecture.md) | Source modules, test layers and data artifacts |
| [Data and Provenance](data-and-provenance.md) | Source-of-truth hierarchy and cumulative search record |
| [Research History](https://rft-sirm.github.io/Phi-Genesis/history.html) | Chronology and reassessment of earlier results |

## Primary research records

The versioned records in the source repository are authoritative. This website organises and explains them but does not supersede them.

- [README and final status](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md)
- [Methodology source](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Binding preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md)
- [Code and tests](https://github.com/RFT-SIRM/Phi-Genesis)

## Scope and evidence discipline

The documented mass relationship \(m=A n\) is a fit, not a spectral prediction: the target indices have not been independently derived by an operator invariant. The tested search families do not satisfy the preregistered selection criterion, and this negative result is bounded to the families and parameter ranges tested.

Phi-Genesis is not a formalization of Evgeny's Theorem. Its numerical status does not inherit the Lean verification status of that separate theorem; the operators, observables and evidence types differ.

## Research correspondence

For scientific correspondence, methodological criticism or reproducibility feedback, contact [**the Phi-Genesis research team**](mailto:evgeniyzaprudnov@gmail.com?subject=Phi-Genesis%20research%20enquiry).

---

_Copyright 2026 · RFT-SIRM · Phi-Genesis Spectral Research Laboratory._
