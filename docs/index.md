# Phi-Genesis — Spectral Research Laboratory

**A reproducible investigation of spectral structure and decimation on graph approximations of the Sierpiński gasket.**

Phi-Genesis is a research laboratory for testing spectral patterns against explicit calculations, reproducible code, and preregistered protocols. The site separates the research record from its visual presentation: numerical evidence is not automatically a theorem, and unresolved questions remain clearly marked.

> **Current documented status · v2.2.1**
>
> The spectral audit is ongoing. Gate A is not presented as fully closed, Open Problem #2 remains unresolved, and the proposed special behaviour at indices \(\{1,12,17,40\}\) is not claimed as established.

## Start here

<div class="grid cards" markdown>

-   :material-flask-outline:{ .lg .middle } **Research programme**

    ---

    Read the scope of the audit, its evidence boundaries, and the questions still open.

    [Research status and questions](#research-status)

-   :material-animation-play-outline:{ .lg .middle } **Interactive portal**

    ---

    Explore the separate animated visual overview. This is the site's single interactive research portal; it complements, rather than replaces, the source records.

    [Open the interactive portal](https://rft-sirm.github.io/Phi-Genesis/interactive/){ .md-button .md-button--primary }

-   :material-clipboard-check-outline:{ .lg .middle } **Methods and reproducibility**

    ---

    Follow the methodology, protocol ledger, preregistration, and versioned records used to assess claims.

    [Open the methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)

-   :material-timeline-clock-outline:{ .lg .middle } **Research history**

    ---

    Read the chronological field notes and the reasoning behind the project's current evidence boundaries.

    [Read research history](history.html)

</div>

## Research programme

The project studies spectral and decimation behaviour associated with finite graph approximations of the Sierpiński gasket. Candidate patterns are checked against computational evidence and documented protocols before being assigned any stronger status.

The public record distinguishes:

- **Established results** — statements supported by their definitions, derivations, or formal verification.
- **Finite-level numerical evidence** — observations reproduced for specified graph levels, parameters, and implementations; these do not alone prove an all-level identity.
- **Open questions** — claims for which the current evidence remains incomplete, negative, or inconclusive.

## Research status

<div class="grid" markdown>

<div class="card" markdown>

### Gate A · Decimation diagnostics

The diagnostic work identifies where low-level matching fails to reach a complete match. The current record does not claim that the full recursively generated exceptional set has been eliminated or that Gate A is closed.

</div>

<div class="card" markdown>

### Spectral inertia

The repository contains a reproducible computational path for inertia experiments on finite graph approximations. Results are bounded to the tested instances and numerical method.

</div>

<div class="card" markdown>

### Open Problem #2

The window-free chord-estimator question remains unresolved. Smoothing does not erase the documented spread across three-period windows.

</div>

<div class="card" markdown>

### Targeted mass indices

The proposed special behaviour at indices \(\{1,12,17,40\}\) is not treated as a confirmed result. The current test and protocol records govern what can be claimed.

</div>

</div>

## Primary research records

The repository's documents, code, tests, and protocol history are the authoritative record. Use these links to inspect the research rather than relying on a summary or visualization.

| Record | What it documents |
|---|---|
| [README and project overview](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md) | Scope, current status, and reproduction entry points |
| [Methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md) | Computational approach and methodological limits |
| [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md) | Audit trail of protocol and analysis decisions |
| [Preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md) | Versioned preregistered research plan |
| [Earlier preregistration record](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION.md) | Historical protocol context |
| [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md) | Version history |
| [Source and tests](https://github.com/RFT-SIRM/Phi-Genesis) | Code, test suite, data, and implementation |

## Contact

For scientific correspondence, methodological criticism, or reproducibility questions, contact [evgeniyzaprudnov@gmail.com](mailto:evgeniyzaprudnov@gmail.com?subject=Phi-Genesis%20research%20enquiry).

---

*Phi-Genesis · Spectral Research Laboratory · documented project status v2.2.1. Visual pages are navigational aids; scientific claims should be checked against the linked source records.*
