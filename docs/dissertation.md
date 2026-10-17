# Research Dissertation

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


<div class="grid cards" markdown>

-   :material-book-open-variant:{ .lg .middle } **Original dissertation**

    ---

    The complete mathematical research synthesis is maintained in its original repository. This page is a curated orientation and navigation guide—not a duplicate of the source manuscript.

    [Read the complete dissertation :material-arrow-top-right:](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)

-   :material-graph-outline:{ .lg .middle } **Related spectral programme**

    ---

    Phi-Genesis investigates signed \(\mathbb{Z}_2\)-flux Laplacians, spectral decimation, finite-level counts, and an exploratory mass-index hypothesis.

    [Explore the interactive portal :material-arrow-top-right:](https://rft-sirm.github.io/Phi-Genesis/interactive/)

-   :material-book-check-outline:{ .lg .middle } **Evidence boundaries**

    ---

    The dissertation distinguishes a specified fourth-moment formalization, finite-level certificates, numerical holdouts, conjectures, and open all-level recurrence questions.

    [Read the Theory of Everything repository README :material-arrow-top-right:](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/README.md)

</div>

## Research Dissertation

**Recursive Graph Operators, Spectral Trace Defects, and Higher-Moment Recurrence**

| Bibliographic field | Record |
|---|---|
| Author | Evgeny Zaprudnov |
| Research group | RFT-SIRM |
| Version | 1.0 |
| Date shown in the source | 15 October 2026 |
| Canonical manuscript | [`DISSERTATION.md`](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md) |
| Source repository | [Evgeny's Theory of Everything](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything) |

!!! info "Why the complete manuscript stays in its original repository"
    The dissertation contains mathematical notation, formulas, proof boundaries, finite-level certificates, numerical tables, and references. Linking to the canonical source avoids maintaining a second, potentially divergent copy inside Phi-Genesis. This page provides context and direct navigation; it is not a replacement manuscript.

## What the dissertation covers

| Strand | Subject | Evidence boundary |
|---|---|---|
| Recursive graph operators | Graph approximations and operator constructions on the Sierpiński gasket | Definitions and results are scoped to the stated construction |
| Fourth-moment trace defect | A concrete identity for a specified SU(2)-connected operator | The source project reports a Lean 4 formalization for the concrete proposition |
| Higher even moments | \(H^6\), \(H^8\), and \(H^{10}\) coefficient/recurrence research | Finite-level certificates and numerical holdouts are not the same as an all-level proof |
| Signed-flux spectral work | \(\mathbb{Z}_2\)-flux, spectral decimation, and boundary/corner corrections | This is a distinct operator programme; Gate A and the mass-index rule remain open in Phi-Genesis |
| Research methodology | Reproducibility, explicit exceptions, numerical holdouts, and open problems | Claims must be interpreted at the evidence level recorded in the source |

## A mathematical anchor: the fourth-moment identity

The theorem repository states the following identity for its specified operators and assumptions:

\[
\Delta_m(H^4,\theta)
=\operatorname{Tr}(H_C^4)-\operatorname{Tr}(H_{C'}^4)
=-16\left(3^{m-1}+1\right)\sin^2\!\left(\frac{\theta}{2}\right),
\qquad m\ge1.
\]

The normalized quantity is defined as

\[
I_m(\theta)=\frac{\Delta_m(H^4,\theta)}{3^{m+1}+3},
\qquad
\lim_{m\to\infty}I_m(\theta)
=-\frac{16}{9}\sin^2\!\left(\frac{\theta}{2}\right).
\]

At \(\theta=\pi/2\), the limiting value is \(-8/9\).

!!! warning "Scope of the theorem"
    The formula above belongs to the concrete fourth-moment proposition in the [Evgeny-Theorem source repository](https://github.com/RFT-SIRM/Evgeny-Theorem). It does not, by itself, establish the higher-moment all-level recurrence, close Phi-Genesis Gate A, derive the indices \(\{1,12,17,40\}\), prove a physical mass law, or establish a complete physical Theory of Everything.

## How this relates to Phi-Genesis

The two projects are related research strands, but they use different mathematical objects and answer different questions.

| | Evgeny-Theorem / dissertation strand | Phi-Genesis strand |
|---|---|---|
| Operator focus | A specified SU(2)-connected graph operator | Signed \(\mathbb{Z}_2\)-flux / \(\pi\)-flux Laplacians |
| Main observable | Fourth-moment trace defect and related higher-moment questions | Low-lying spectrum, gaps, decimation, and candidate mass indices |
| Strongest stated evidence | A concrete fourth-moment Lean formalization; finite-level higher-moment certificates and holdouts | Reproducible numerical checks and preregistered selection searches |
| Key unresolved question | Proving the proposed higher-moment recurrence for all stated levels/angles from the recursive structure | Characterizing the full decimation exceptional set and deriving target indices independently |
| Does one establish the other? | No | No |

A formal proof in one repository does not transfer automatically to another operator, observable, or physical interpretation. A bridge between these constructions would need its own definitions, assumptions, derivation, and verification.

## Research links

- [**Complete dissertation — canonical source**](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md)
- [Theory of Everything repository README](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/README.md)
- [Fourth-moment theorem statement](https://github.com/RFT-SIRM/Evgeny-Theorem/blob/main/THEOREM.md)
- [Lean formalization](https://github.com/RFT-SIRM/Evgeny-Theorem/tree/main/formalization)
- [Verification record](https://github.com/RFT-SIRM/Evgeny-Theorem/blob/main/VERIFICATION.md)
- [Theory of Everything higher-moment recurrence note](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/computational/HIGHER_MOMENT_RECURRENCE_NOTE.md)
- [Theory of Everything independent sparse level-7 holdout](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/computational/HIGHER_MOMENT_SPARSE_LEVEL7.md)
- [Phi-Genesis methodology](methodology.md)
- [Phi-Genesis open problems](open-problems.md)
- [Return to the interactive Phi-Genesis portal](https://rft-sirm.github.io/Phi-Genesis/interactive/)

---

*This page is an orientation layer. The original repository remains authoritative for the dissertation's full mathematical content, provenance, version history, and evidence status.*

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
