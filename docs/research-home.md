# Phi-Genesis — Spectral Research Home

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Lean 4](https://img.shields.io/badge/Lean%204-formalized-168f83?style=flat-square)

**The central result of Phi-Genesis is a formally verified convergence theorem for the least eigenvalues of recursively refined Sierpiński-gasket graph operators.**

> **FEATURED MATHEMATICAL RESULT**
>
> An exact three-corner Schur boundary recursion is connected to the graph matrices in Lean 4. For every level $N\geq6$, its selected $A_1$ root is the unique least eigenvalue in an exact rational interval. The least-eigenvalue sequence converges to $\lambda_\infty$ in that interval, whose width is $2\cdot10^{-36}$.
>
> Read the [Schur recursion and limiting spectral constant](spectral-limit.md) and the [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md).

Phi-Genesis combines formal proof, exact finite-level algebra, and high-precision numerical investigation. The repository keeps these evidence types distinct: the Lean theorem proves existence and enclosure of the limit; the 145-digit level-9 value is a finite-level computation; the observed quadratic correction remains a conjectural asymptotic pattern.

## Principal mathematical result

$$
\lambda_N=\lambda_{\min}(Q_N),\qquad
\lambda_N\longrightarrow\lambda_\infty\in[L,U],
\qquad U-L=2\cdot10^{-36}.
$$

Here $Q_N=D_N+A_N$ is the signless graph Laplacian. The specified signed local-face matrix is gauge-conjugate to $Q_N$ and has the same spectrum.

The exact rational endpoints, theorem names, and proof dependencies are given in the [spectral-limit dossier](spectral-limit.md). The separate all-level lower-bound theorem proves that every real eigenvalue of the signed matrix is at least $1$.

## Research strands

| Strand | Main record | Evidence status |
|---|---|---|
| Schur recursion and limiting least eigenvalue | [Spectral-limit dossier](spectral-limit.md) · [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md) | Lean 4: exact recursion, least-eigenvalue identification, convergence, and rational enclosure |
| High-precision finite-level values | [High-precision note](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md) | Numerical finite-level calculation; not a 145-digit proof for the limit |
| Signed local-face operator | [Verified results](verified-results.md) | Gauge equivalence and all-level lower bound are formalized |
| Spectral decimation and spectral dimension | [Research map](research-map.md) · [Open problems](open-problems.md) | Combination of established theory and scoped numerical checks |
| Signed-$Z_2$ H10 moments | [Finite H10 note](higher-moments-z2.md) | Exact finite computations; all-level recurrence remains open |
| Boundary-condition experiments | [Verified results](verified-results.md) | Finite-level computations for specified twists |
| Historical physical applications | [Research archive](selection-protocol.md) | Kept separate from the Schur-limit proof and its dependencies |

## Recommended reading order

1. [Schur recursion and the limiting spectral constant](spectral-limit.md).
2. [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md).
3. [High-precision finite-level calculations](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md).
4. [Verified results and evidence boundaries](verified-results.md).
5. [Open mathematical problems](open-problems.md).
6. [Reproducibility instructions](reproducibility.md).

## Supplementary archive

Separate exploratory physical applications and their statistical protocols are preserved in the [selection-protocol archive](selection-protocol.md), [D₃ representation audit](d3-representation-audit.md), [methodology](methodology.md), and [protocol ledger](protocol-ledger.md). They are distinct research questions and are not premises for the principal spectral-limit theorem.

## Source of truth

The Lean files and versioned computational records are authoritative. The visual portal and summaries provide navigation; they do not upgrade numerical evidence into a formal theorem or alter the scope of a proof.

- [Main repository](https://github.com/RFT-SIRM/Phi-Genesis)
- [Schur boundary recursion](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurBoundary.lean)
- [Least-eigenvalue theorem](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurEigenvalue.lean)
- [High-precision computation](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md)

_Copyright 2026 Evgeny Zaprudnov (RFT-SIRM)._
