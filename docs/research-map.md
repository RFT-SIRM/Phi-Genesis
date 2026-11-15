# Research Map — Phi-Genesis

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Lean 4](https://img.shields.io/badge/Lean%204-formalized-168f83?style=flat-square)

Phi-Genesis studies the spectral theory of recursively refined Sierpiński-gasket graph operators. Its central mathematical result is the Lean 4 proof that the least eigenvalues selected by an exact three-corner Schur recursion converge to a limit enclosed by a rational interval of width $2\cdot10^{-36}$.

The [spectral-limit dossier](spectral-limit.md) is the main entry point. The [interactive portal](https://rft-sirm.github.io/Phi-Genesis/interactive/) is a visual guide; the source repository and proof files remain authoritative.

## Main proof path

<div class="grid cards" markdown>

-   :material-graph-outline:{ .lg .middle } **1. Graph operator and gauge equivalence**

    ---

    The signed local-face matrix is diagonally gauge-conjugate to the signless graph Laplacian $Q_N=D_N+A_N$.

    [Read the formal result](spectral-limit.md#1-operator-and-graph-sequence)

-   :material-vector-polyline:{ .lg .middle } **2. Exact Schur boundary recursion**

    ---

    Eliminating the interior vertices leaves a three-corner boundary response described by two scalar coefficients.

    [Read the recursion dossier](spectral-limit.md#2-exact-three-corner-schur-recursion)

-   :material-function-variant:{ .lg .middle } **3. Least-eigenvalue identification**

    ---

    The selected $A_1$ root is unique in the exact rational interval and equals the least eigenvalue for every $N\geq6$.

    [Read the Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md)

-   :material-chart-timeline-variant:{ .lg .middle } **4. Limiting spectral constant**

    ---

    The least-eigenvalue sequence converges to $\lambda_\infty\in[L,U]$, with exact interval width $2\cdot10^{-36}$.

    [Read the convergence theorem](spectral-limit.md#3-the-lean-convergence-theorem)

-   :material-calculator-variant:{ .lg .middle } **5. High-precision finite-level calculations**

    ---

    The finite-level Schur calculation resolves the nearby low-lying symmetry channels and provides numerical values; it does not replace the Lean limit theorem.

    [Read the numerical note](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md)

-   :material-console:{ .lg .middle } **6. Reproduction and remaining work**

    ---

    Rebuild the formal development, reproduce numerical calculations, and review the open asymptotic and model-identification questions.

    [Reproduce the work](reproducibility.md) · [Open problems](open-problems.md)

</div>

## Supporting research strands

| Strand | Description | Record |
|---|---|---|
| Spectral decimation | Factor-five scaling with graph-boundary corrections and a still-open full exceptional-set characterization | [Verified results](verified-results.md) |
| Spectral dimension | Theoretical exponent and finite-level estimator studies | [Open problems](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent) |
| Boundary conditions | Finite-level signed and $\pi$-flux experiments | [Verified results](verified-results.md) |
| Signed-$Z_2$ moments | Exact finite-level tenth-moment computations for a specified representative | [H10 research note](higher-moments-z2.md) |
| Historical physical applications | Separate exploratory records, not part of the Schur proof chain | [Research archive](selection-protocol.md) |

## Current theorem status

| Claim | Status |
|---|---|
| Signed/signless gauge equivalence | Proved in Lean 4 |
| Uniform lower bound $\lambda\geq1$ for the signed matrix | Proved in Lean 4 at every level |
| Unique selected $A_1$ root equals the least eigenvalue | Proved in Lean 4 for $N\geq6$ |
| Least-eigenvalue convergence and exact rational enclosure | Proved in Lean 4 |
| About 145 displayed digits at level 9 | High-precision finite-level calculation |
| All-level quadratic increment law | Open |
| Unconditional external $\theta=2\pi$ operator identification | Open |

## Reading order

Start with the [spectral-limit dossier](spectral-limit.md), then inspect the [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md), [high-precision note](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md), and [verified results](verified-results.md). The [research archive](selection-protocol.md) contains separate exploratory workstreams and their provenance.
