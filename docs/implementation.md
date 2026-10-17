# Computational Implementation

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


This page describes the implementation evidence at a high level. The repository's source files and fixed data artifacts remain the authority for exact algorithms and results.

## Implementation layers

- Graph construction and boundary-condition setup.
- Sparse matrix assembly and spectral or inertia calculations.
- Spectral counting and finite-window estimator experiments.
- Protocol runners, null-model checks, and fixed-seed data.
- Tests and reproducibility scripts.

## Numerical precautions

- Treat a singular-shift or eigenvalue-coincidence failure as a numerical condition to report, not silently discard.
- Record graph level, vertex count, operator convention, boundary condition, precision, and estimator window.
- Keep corner-defect corrections explicit.
- Do not treat successful code execution as a proof of a mathematical conjecture.

See [Computational Architecture](computational-architecture.md) and [Reproducibility](reproducibility.md).

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
