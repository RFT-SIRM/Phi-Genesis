# Verified Results and Evidence Boundaries

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


This page summarises the results recorded in Phi-Genesis v2.2.1. “Verified” here means supported by the stated derivation, numerical computation or regression test within its stated scope. It does **not** mean that every claim is machine-checked or that finite-level evidence proves a universal theorem.

## 1. Sierpiński-gasket spectral structure

- **Spectral decimation:** the characteristic eigenvalue scale factor is 5 between consecutive levels, with corner-defect corrections for the corner-degree-2 Laplacian used in this repository.
- **Fukushima–Shima gaps:** the computations recover forbidden zones associated with fixed points near \(\lambda\approx2.5\) and \(\lambda\approx3\).
- **Log-periodic structure:** the counting data exhibit the expected periodic signature associated with the factor-5 scaling.

These statements concern the graph family, operator convention and finite-level checks documented in the source. Start with [source code](https://github.com/RFT-SIRM/Phi-Genesis/tree/main/phi_genesis) and the [README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md).

## 2. Weyl exponent and finite-level estimates

For the Sierpiński gasket, the theoretical exponent is

\[
\frac{d_s}{2}=\frac{\ln 3}{\ln 5}\approx0.6826.
\]

The repository reports that a window-free chord estimator is within 0.1% of its stated comparison expression at level 9 for \(N\ge1000\). This is a result for that estimator and range, not proof that every finite-level estimator converges uniformly.

The inertia-based count path uses Sylvester's law of inertia with sparse LU rather than computing the full spectrum. The documented level-10 graph has 88,575 vertices. The reported resource figures and window studies are implementation- and parameter-specific; see [Open Problem #2](open-problems.md#2-finite-level-convergence-of-the-spectral-exponent) and the [reproduction guide](reproducibility.md).

## 3. Möbius / π-flux boundary conditions

For the tested level-5 graph, the documented full π-flux configuration raises the first eigenvalue from approximately 0.006 to approximately 0.46, opening a spectral gap in that instance. Partial twists also produce gaps in the tested cases.

This does **not** establish a selection mechanism for \(\{1,12,17,40\}\). In the exhaustive search of all \(2^5=32\) generation-twist configurations, the maximum simultaneous target hit was 1 of 4 and index 40 was never selected.

## 4. Integer mass fit — a fit, not a prediction

The repository records a single-scale fit \(m=A n\), with \(A=104.63\) MeV and integer indices \(n=\{1,12,17,40\}\), matching four selected masses with a mean error of about 0.68%.

The index set was chosen with the masses in view. Because no independent spectral rule has derived those indices, this numerical agreement is **not a prediction** and must not be described as a confirmed mass law. The alternative scale expression documented in the README gives approximately 100.13 MeV, about 4.3% below the fitted value.

The top-quark index is unresolved: the repository documents candidates 1654, 1664 and 1680 arising from different procedures/scales. No single candidate is endorsed.

## 5. η-invariant claim — not reproduced

The RFT-String v8.7 claim \(\bar\eta(0)=-4\) for the stated boundary potential was not reproduced. The documented test reports asymmetry +1 for the claimed potential, −1 for a random potential, and −2 for zero potential; −4 was not observed in the tested cases. The repository interprets the observed asymmetry as a finite-size effect, not as a demonstrated topological invariant.

## 6. How to read the evidence { #how-to-read-the-evidence }

| Label | Interpretation |
|---|---|
| Theoretical identity | Follows from specified mathematical definitions and assumptions. |
| Reproducible numerical result | A computation can be rerun for the documented finite instance and implementation. |
| Fit / estimator output | Depends on model choice, parameter range and estimator design. |
| Negative search result | The tested family did not meet its predeclared criterion; it does not prove no mechanism exists anywhere. |
| Open problem | Current evidence is incomplete, inconclusive, or sensitive to a remaining methodological choice. |

Phi-Genesis' numerical results are not automatically formal proofs. In particular, the Lean-verified status of [Evgeny's Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem) does not transfer to this repository: the operator families, observables and verification methods differ.

## Primary sources

- [Project README and final status](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md)
- [Methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Automated tests and source](https://github.com/RFT-SIRM/Phi-Genesis)

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
