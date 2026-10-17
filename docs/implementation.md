# Computational Implementation

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
