# Research Map — Phi-Genesis

Phi-Genesis is the spectral-computation branch of the RFT-SIRM research programme. It investigates spectral decimation, spectral gaps, finite-level spectral counts, and whether a proposed set of integer indices can be selected by a spectral rule on Sierpiński-gasket graph approximations.

This map is an evidence-first guide to the project. The [interactive portal](https://rft-sirm.github.io/Phi-Genesis/interactive/) is a visual overview; the source repository, code, preregistration and ledger remain authoritative.

## Research strands

<div class="grid cards" markdown>

-   :material-graph-outline:{ .lg .middle } **1. Sierpiński-gasket spectrum**

    ---

    Graph Laplacians, spectral decimation, Fukushima–Shima gaps and the role of corner-defect corrections.

    [Read verified results](verified-results.md)

-   :material-chart-bell-curve:{ .lg .middle } **2. Spectral dimension and counting**

    ---

    Weyl counting, finite-level estimates and the sensitivity of regression fits to the log-periodic window.

    [Read Open Problem #2](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent)

-   :material-tune-vertical:{ .lg .middle } **3. Boundary twists and gap selection**

    ---

    Möbius / π-flux boundary conditions, generation twists and tests of candidate index-selection rules.

    [Read the protocol audit](selection-protocol.md)

-   :material-clipboard-check-outline:{ .lg .middle } **4. Preregistered search**

    ---

    The target indices \(\{1,12,17,40\}\), null ensembles, power checks and cumulative search ledger.

    [Inspect protocol results](selection-protocol.md)

-   :material-scale-balance:{ .lg .middle } **5. Claim and evidence control**

    ---

    Distinguish a numerical fit, a reproducible finite-level computation, a conjecture and a theorem.

    [Read the evidence policy](verified-results.md#how-to-read-the-evidence)

-   :material-console:{ .lg .middle } **6. Reproduction**

    ---

    Test commands, fixed-seed protocol runs and the scripts used for the finite-level estimator study.

    [Reproduce the work](reproducibility.md)

</div>

## Current research status

**Documented release:** v2.2.1. The repository records reproducible numerical observations and negative results, but does not claim a derived selection rule for the target mass indices.

| Question | Current status | What the status means |
|---|---|---|
| Spectral decimation | Supported with stated corrections | The factor-5 structure is subject to corner-defect corrections for the graph Laplacian used here. |
| Fukushima–Shima gaps | Numerically reproduced | Finite-level computations support the documented gap structure. |
| π-flux boundary conditions | Gap observed in tested cases | This does not by itself select the target mass indices. |
| Selection of \(\{1,12,17,40\}\) | Not found | Preregistered families did not meet the specified criterion after look-elsewhere correction. |
| Spectral exponent estimation | Partly characterised; open | The theoretical exponent is known, but finite-window estimates depend on estimator and window choice. |
| η-invariant claim from RFT-String v8.7 | Not reproduced | The reported value −4 was not observed in the tested cases. |

## Reading order

1. Start with [Verified Results](verified-results.md) for the claims and their limits.
2. Read the [Selection Protocol](selection-protocol.md) and [Open Problems](open-problems.md) to understand negative results and remaining work.
3. Use [Reproducibility](reproducibility.md) to rerun the relevant tests.
4. Check the original [README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md), [methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md), [protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md), and [preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md).

## Scope boundary

Phi-Genesis is not a formal proof repository for Evgeny's Theorem, and its computational status does not inherit the Lean verification status of that separate theorem. The theorem and this spectral audit concern different operators, observables and evidence types. See the [project README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md#scope-relation-to-evgenys-theorem).
