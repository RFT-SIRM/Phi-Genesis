# Schur Recursion and the Limiting Spectral Constant

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Limit-147fba?style=flat-square) ![Lean 4](https://img.shields.io/badge/Lean%204-formalized-168f83?style=flat-square)

**Principal result.** The least eigenvalues of the recursively defined Sierpiński-gasket graph Laplacians form a convergent sequence. The convergence theorem, the least-eigenvalue identification, and the exact rational enclosure are formalized in Lean 4.

## 1. Operator and graph sequence

Let $Q_N=D_N+A_N$ be the signless graph Laplacian of the level-$N$ Sierpiński-gasket graph. The signed local-face matrix is

$$
H_N=D_N+A_{s,N}.
$$

The Lean development proves that the signed matrix is diagonally gauge-conjugate to the signless matrix:

$$
H_N=G_N Q_N G_N,
$$

where $G_N$ is the diagonal vertex-gauge matrix and $G_N^2=I$. Hence the two finite matrices have the same spectrum.

Write $\lambda_N$ for their common least eigenvalue.

## 2. Exact three-corner Schur recursion

Eliminating the interior vertices leaves a three-corner boundary response. By the $S_3$ symmetry of the boundary, it is described by a diagonal coefficient $\alpha_N(\lambda)$ and an off-diagonal coefficient $\beta_N(\lambda)$. The distinguished scalar characteristic is the constant-boundary channel:

$
F_N(\lambda)=a_N(\lambda)+2b_N(\lambda).
$

The exact Schur update is connected to the actual recursively assembled graph matrices. The formal proof covers the midpoint pivots, the boundary-response bridge, and the nonnegativity/inertia argument needed to identify the selected root with the least eigenvalue.

## 3. The Lean convergence theorem

For every $N=6+n$, the selected $A_1$ root is the unique root of $F_N$ in the exact interval $[L,U]$ and equals the least eigenvalue of $Q_N$. The least-eigenvalue sequence converges:

$$
\exists\,\lambda_\infty\in[L,U],\qquad
\lambda_N\longrightarrow\lambda_\infty
\quad(N\to\infty).
$$

The interval endpoints are exact rationals:

$$
L=\frac{1309128920280813421888623088170810187}{10^{36}},
\qquad
U=\frac{1309128920280813421888623088170810189}{10^{36}}.
$$

$$
U-L=2\cdot10^{-36},
\qquad
\lambda_\infty\in[L,U].
$$

This is an exact existence-and-enclosure theorem, not a floating-point estimate. The limiting value is also proved to be a zero of the uniformly limiting $A_1$ characteristic.

The formal proof chain includes:

| Mathematical step | Lean theorem | Source |
|---|---|---|
| Signed/signless gauge equivalence | sgSignedLaplacianMatrix_eq_gauge_conj | [SchurBridge.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurBridge.lean) |
| Graph-matrix boundary response follows the Schur recursion | sgCornerResponse_trajectory_bootstrap | [SchurCornerTrajectory.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurCornerTrajectory.lean) |
| Root uniqueness in $[L,U]$ | schurBootstrapA1Root_unique | [SchurLambdaMin.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurLambdaMin.lean) |
| Selected root is the least eigenvalue | sgChosenRoot_isLeast | [SchurEigenvalue.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurEigenvalue.lean) |
| Least-eigenvalue convergence | sgLeastEigenvalue_converges | [SchurEigenvalue.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurEigenvalue.lean) |
| Limit is a zero of the limiting characteristic | schurBootstrapA1AtLevel_rootLimit_is_root | [SchurBoundary.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurBoundary.lean) |
| Transfer to the signed matrix | sgSignedLeastEigenvalue_converges | [SchurSignedTransfer.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurSignedTransfer.lean) |
| Uniform lower bound at every level | sgSignedLaplacianMatrix_eigenvalue_ge_one | [SignedLaplacianMatrix.lean](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean) |

The uniform lower bound $1$ is a separate all-level theorem. It does not replace the convergence theorem; it provides an independent positive lower bound for every refinement level.

## 4. Numerical finite-level values

The high-precision Schur calculation reports the following bottom eigenvalues:

| Level $N$ | Dimension | Finite-level numerical $\lambda_N$ |
|---:|---:|---:|
| 4 | 123 | $1.3091289186270032373372269265507617266049\ldots$ |
| 5 | 366 | $1.3091289202808134205376249464114593830015\ldots$ |
| 9 | 29,526 | $1.3091289202808134218886230881708101885523\ldots$ |

The level-9 calculation is stable to about 145 displayed decimal places in the high-precision run. Those are digits of a finite-level computation. They are **not** a 145-digit certified expansion of $\lambda_\infty$.

The observed ratios

$$
\frac{\lambda_{N+1}-\lambda_N}
     {(\lambda_N-\lambda_{N-1})^2}
\approx0.4939504899
$$

are numerical evidence for a quadratic increment law. The all-level law and its coefficient have not yet been proved.

See the [high-precision computation note](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/HIGH_PRECISION_2026-11-06.md) and the [reproducible Schur script](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/schur_bottom_eigenvalue.py).

## 5. What remains open

1. Sharpen the rigorously certified enclosure of $\lambda_\infty$ and seek an analytic or algebraic characterization where one exists.
2. Prove the all-level quadratic increment law and determine its coefficient.
3. Prove an unconditional source-to-source identification of this local-face matrix model with the external $\theta=2\pi$ operator.
4. Complete the characterization of the exceptional set for the graph's spectral-decimation correspondence.

These are refinements and extensions of the established convergence theorem. They do not negate the theorem or its exact rational enclosure.

## 6. Reproduction

From the repository root:

~~~bash
lake build PhiGenesis
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/schur_bottom_eigenvalue.py
~~~

The Lean build checks the formal theorem. The Python calculation reproduces finite-level numerical values; it is not used as a premise in the Lean proof.

Primary sources: the [Lean proof map](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/spectral_gap_theta_2pi/PROOF_MAP.md), [Schur boundary recursion](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurBoundary.lean), [least-eigenvalue theorem](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurEigenvalue.lean), and [signed transfer](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PhiGenesis/SpectralGap/SchurSignedTransfer.lean).
