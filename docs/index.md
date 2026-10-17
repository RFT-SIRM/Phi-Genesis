# Phi-Genesis — Spectral Research Laboratory

**Spectral structure, decimation and reproducible computation on Sierpiński-gasket graph approximations.**

Phi-Genesis is an independent computational research programme. It tests proposed spectral patterns against explicit calculations, preregistered protocols and an auditable history of both positive and negative results. The laboratory's central discipline is to distinguish a mathematical statement from a finite numerical observation, a fitted relationship and an open conjecture.

> **Current documented status · v2.2.1**
>
> The spectral audit remains bounded by its evidence. The tested search families have not established an independent selection rule for the target indices \(\{1,12,17,40\}\); Open Problem #2 remains open; and numerical results are not presented as machine-checked theorems.

## Laboratory navigation

<div class="grid cards" markdown>

-   :material-map-outline:{ .lg .middle } **Research map**

    ---

    A structured overview of the research strands, status labels, and the recommended reading order.

    [Explore the research map](research-map.md)

-   :material-chart-box-outline:{ .lg .middle } **Results and evidence**

    ---

    Spectral gaps, decimation, Weyl estimates, π-flux experiments, and what each result does—and does not—establish.

    [Review verified results](verified-results.md)

-   :material-clipboard-check-outline:{ .lg .middle } **Selection protocol**

    ---

    Preregistered families, null models, power checks, p-values, and the cumulative search ledger.

    [Read the protocol audit](selection-protocol.md)

-   :material-puzzle-outline:{ .lg .middle } **Open problems**

    ---

    The missing independent index-selection rule, finite-level estimator sensitivity, and model requirements for further physics-facing work.

    [Review open problems](open-problems.md)

-   :material-console-line:{ .lg .middle } **Computational architecture**

    ---

    Source modules, numerical pathways, tests, protocol data, and how the evidence artifacts fit together.

    [Explore the code architecture](computational-architecture.md)

-   :material-play-circle-outline:{ .lg .middle } **Interactive portal**

    ---

    A single, separate animated visualization of the research. It complements this documentation and does not replace source records.

    [Open the interactive portal](https://rft-sirm.github.io/Phi-Genesis/interactive/){ .md-button .md-button--primary }

</div>

## Research programme

The work centres on five connected strands:

1. **Spectral decimation and gap structure.** Investigate the factor-5 spectral structure of finite Sierpiński-gasket graph approximations, including corner-defect corrections and the documented Fukushima–Shima gaps.
2. **Spectral dimension and counting.** Compare eigenvalue-counting estimates and study how finite graph level and log-periodic fitting windows affect exponent estimates.
3. **Boundary conditions and flux.** Test how Möbius / π-flux conditions and generation twists alter the low-lying spectrum and gap-selected positions.
4. **Statistical selection audit.** Test whether a spectral rule independently selects the proposed indices \(\{1,12,17,40\}\), with preregistered null ensembles and correction for the number of configurations tried.
5. **Evidence and provenance.** Preserve the protocol history, including negative and exploratory results, so that earlier coincidences are not later mistaken for independent predictions.

## Current evidence at a glance { #verified }

| Research question | Documented position |
|---|---|
| Factor-5 spectral decimation | Supported with corner-defect corrections for the documented Laplacian |
| Fukushima–Shima gap structure | Numerically reproduced in the documented tests |
| Full π-flux condition | Opens a gap in the tested level-5 instance |
| Selection of \(\{1,12,17,40\}\) | Not established; preregistered tests did not meet the threshold |
| Window-free chord estimator | Reported within 0.1% of its stated comparison expression at level 9 for \(N\ge1000\) |
| Robust finite-level convergence | Still open; regression results depend on window choice |
| Claimed η-invariant value −4 | Not reproduced in the documented tests |

These summaries are scoped to the tested graph levels, operator definitions, numerical procedures and protocol families. Full details and caveats are on [Verified Results](verified-results.md), [Selection Protocol](selection-protocol.md), and [Open Problems](open-problems.md).

## Methods, protocols and provenance

The laboratory uses separate records for different purposes:

- [Methodology](methodology.md) — why the search uses null models, target base rates, maximum-over-family statistics and null-only power checks.
- [Reproducibility](reproducibility.md) — test commands, fixed-seed protocol commands, estimator scripts and data-preservation cautions.
- [Computational Architecture](computational-architecture.md) — modules, test layers and data artifacts.
- [Data and Provenance](data-and-provenance.md) — source-of-truth hierarchy, cumulative counts and interpretation safeguards.
- [Research History](history.html) — chronological field notes and reassessment of earlier results.

The versioned primary records remain authoritative: [README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md), [METHODOLOGY.md](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md), [protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md), [preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md), and [changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md).

## Scope and scientific discipline

Phi-Genesis is a computational spectral audit, not a formalization of Evgeny's Theorem. That theorem has its own operator definitions, observable and Lean verification record; its formal status does not transfer to this repository's spectral calculations or mass-index search.

The mass relationship \(m=A n\) remains a numerical fit rather than a spectral prediction because the target indices have not been independently derived by an operator invariant. The repository records this limitation explicitly.

## Research correspondence

For scientific correspondence, methodological criticism, or reproducibility feedback, use the email link below. The address is intentionally displayed as a short action rather than a long raw string so it remains contained on narrow screens.

[**Contact the laboratory**](mailto:evgeniyzaprudnov@gmail.com?subject=Phi-Genesis%20research%20enquiry){ .md-button }

---

*Phi-Genesis · Spectral Research Laboratory · documented project status v2.2.1. Visual pages are navigational aids; claims should be checked against the linked primary records.*
