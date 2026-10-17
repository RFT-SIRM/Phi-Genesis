# Computational Architecture

This page is a map of the code and research artifacts in the repository. It does not replace source code, tests or versioned research records.

## Main computational modules

| Module / area | Responsibility |
|---|---|
| \`phi_genesis/sg_laplacian.py\` | Sierpiński-gasket graph Laplacian, decimation and Weyl-related calculations |
| \`phi_genesis/fukushima_shima.py\` | Fukushima–Shima gap-structure checks |
| \`phi_genesis/spectral_convergence.py\` | Dense spectral calculations, Weyl fits and window-sensitivity analysis |
| \`phi_genesis/sg_inertia.py\` | Eigenvalue counts from Sylvester inertia with sparse LU |
| \`phi_genesis/mobius.py\` | Signed Laplacian and π-flux / Z₂ twist operations |
| \`phi_genesis/mobius_selection_search.py\` | Exhaustive generation-twist selection search |
| \`phi_genesis/dirac_eta.py\` | Graph Dirac operator and η-invariant claim checks |
| \`phi_genesis/mass_check.py\` | Mass-scale consistency calculations |
| \`phi_genesis/selection_protocol*.py\` | Versioned preregistered selection tests |

The current file tree and test suite are available in the [GitHub repository](https://github.com/RFT-SIRM/Phi-Genesis/tree/main).

## Research data and audit artifacts

- \`protocol_data/\` contains null pools, protocol outputs, design results and Open Problem #2 scripts.
- \`PREREGISTRATION*.md\` records the rules and design decisions for each protocol version.
- \`protocol_ledger.md\` records the cumulative family search and post-hoc diagnostics.
- \`METHODOLOGY.md\` explains the statistical method and its limits.
- \`CHANGELOG.md\` records documentation and release changes.

## Verification layers

The project combines unit tests, numerical cross-checks and preregistered statistical tests. These answer different questions:

- A unit test checks a specific implementation property.
- A dense-spectrum comparison checks a numerical path against a smaller reference instance.
- A preregistered null test evaluates whether a search result exceeds the specified chance baseline.
- A theoretical derivation is needed for a general mathematical statement.

Passing one layer does not automatically establish claims that belong to another.

## Reproduction

See the [Reproducibility guide](reproducibility.md) for commands and warnings about regenerating fixed-seed data. Start from a clean checkout when preserving the committed protocol pools matters.
