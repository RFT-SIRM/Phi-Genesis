# Verified Results and Evidence Boundaries

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Lean 4](https://img.shields.io/badge/Lean%204-formalized-168f83?style=flat-square)

This page puts the principal mathematical result first and distinguishes formal theorems from finite-level numerical and computational records.

## 1. Schur recursion and convergence of the least eigenvalue

For the signless graph Laplacian $Q_N=D_N+A_N$, the exact three-corner Schur recursion selects a unique $A_1$ root in an exact rational interval for each $N\geq6$. Lean 4 proves that this root is the least eigenvalue and that the least-eigenvalue sequence converges to $\lambda_\infty$ in that interval.

The endpoints are exact rationals:

$$
L=\frac{1309128920280813421888623088170810187}{10^{36}},
\qquad
U=\frac{1309128920280813421888623088170810189}{10^{36}}.
$$

$$
\lambda_\infty\in[L,U],
\qquad U-L=2\cdot10^{-36}.
$$

The signed local-face matrix is gauge-conjugate to $Q_N$, so it has the same spectrum. The limiting value is also a zero of the limiting $A_1$ characteristic.

**Lean theorems:** schurBootstrapA1Root_unique, sgChosenRoot_isLeast, sgLeastEigenvalue_converges, sgSignedLeastEigenvalue_converges, and schurBootstrapA1AtLevel_rootLimit_is_root.

See the [spectral-limit dossier](spectral-limit.md), [proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md), and source files [SchurLambdaMin.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurLambdaMin.lean) and [SchurEigenvalue.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurEigenvalue.lean).

## 2. Uniform lower bound for the signed graph Laplacian

Every real eigenvalue of the explicitly defined signed graph Laplacian, represented by a nonzero real eigenvector, is at least $1$ at every refinement level. The matrix is expressed as a sum of rank-one edge contributions, and its quadratic form is identified with the signed graph energy.

**Lean theorem:** sgSignedLaplacianMatrix_eigenvalue_ge_one in [SignedLaplacianMatrix.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean).

## 3. Sierpiński-gasket spectral structure

- **Spectral decimation:** the characteristic eigenvalue scale factor is 5 between consecutive levels, with corner-defect corrections for the corner-degree-2 Laplacian used in this repository.
- **Fukushima–Shima gaps:** computations recover forbidden zones associated with fixed points near $\lambda\approx2.5$ and $\lambda\approx3$.
- **Log-periodic structure:** counting data exhibit the expected periodic signature associated with the factor-five scaling.

These statements concern the graph family, operator convention, and finite-level checks documented in the source. They are numerical/computational observations, not substitutes for the Lean convergence theorem.

## 4. Spectral dimension and finite-level estimates

For the Sierpiński gasket, the theoretical exponent is

$$
\frac{d_s}{2}=\frac{\ln3}{\ln5}\approx0.6826.
$$

The repository reports that a window-free chord estimator is within 0.1% of its stated comparison expression at level 9 for the documented $N\geq1000$ subset. This is a result for that estimator and range, not proof that every finite-level estimator converges uniformly. The inertia-based count path uses Sylvester's law of inertia with sparse LU; the documented level-10 graph has 88,575 vertices.

See [Open Problem 5](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent) and the [reproduction guide](reproducibility.md).

## 5. Möbius and $\pi$-flux boundary conditions

For the tested level-5 graph, the documented full-$\pi$-flux configuration raises the first eigenvalue from approximately 0.006 to approximately 0.46, opening a spectral gap in that instance. Partial twists also produce gaps in the tested cases.

These are finite-level boundary-condition results for the stated graph and operator convention. They form a separate computational strand and are not used as premises in the Schur-limit proof.

## 6. Signed-$Z_2$ H10 finite computation

For the deterministic GF(2) representative used by the hole-boundary solver, exact sparse-integer calculations give

$$
D_m^{(10)}=
\operatorname{Tr}(L_{\pi,m}^{10})-
\operatorname{Tr}(L_{0,m}^{10}).
$$

The traces are computed through level 10. The residual $D_m^{(10)}-3D_{m-1}^{(10)}$ equals 12,387,360 on transitions 3→4 through 9→10. Complete generation-twist sweeps were computed at levels 4–9, with 1,008 transition checks; 156 level-10 samples agree with the recurrence. The recurrence is not yet an all-level theorem.

Hole-boundary parities do not determine a unique cocycle. At level 5, 243 elementary-triangle holonomy degrees of freedom remain, and changing the local representative while preserving hole parities changes H10. This is not a topological invariant of hole flux alone. The scalar signed operator is distinct from the SU(2) operator in Evgeny-Theorem.

See the [full finite H10 note](higher-moments-z2.md), implementation, and reproduction instructions.

## 7. Separate historical physical applications

The repository retains an exploratory integer-index mass-fit study and its associated spectral-selection protocols as a distinct research archive. Those records document their own assumptions, numerical calculations, statistical design, and limitations. They are not part of the definition or proof dependency graph of the limiting spectral constant.

For those records, see [Selection Protocol](selection-protocol.md), [D₃ Representation Audit](d3-representation-audit.md), [Methodology](methodology.md), and [Protocol Ledger](protocol-ledger.md).

## 8. η-invariant claim — not reproduced

The RFT-String v8.7 claim $\bar\eta(0)=-4$ for the stated boundary potential was not reproduced. The documented test reports asymmetry +1 for the claimed potential, −1 for a random potential, and −2 for zero potential; −4 was not observed in the tested cases. The repository interprets the observed asymmetry as a finite-size effect, not as a demonstrated topological invariant.

## 9. How to read the evidence { #how-to-read-the-evidence }

| Label | Interpretation |
|---|---|
| Theoretical identity | Follows from specified mathematical definitions and assumptions. |
| Lean 4 formal theorem | A proposition accepted by the Lean kernel for the stated definitions and assumptions. |
| Reproducible numerical result | A computation can be rerun for the documented finite instance and implementation. |
| Fit / estimator output | Depends on model choice, parameter range, and estimator design. |
| Open problem | Current evidence is incomplete or a proof obligation remains. |

The finite-level numerical results are not automatically formal proofs. The Lean-verified status of [Evgeny's Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem) does not transfer to this repository: the operator families, observables, and verification methods differ.

## Primary sources

- [Spectral-limit dossier](spectral-limit.md)
- [Project README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md)
- [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md)
- [High-precision numerical note](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md)
- [Source repository](https://github.com/RFT-SIRM/Phi-Genesis)
