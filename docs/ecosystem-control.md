# Ecosystem Control Plane

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


Phi-Genesis participates in the RFT-SIRM research ecosystem. The automated status collector reads the latest public GitHub Actions run for each registered repository and publishes a Markdown summary and JSON artifact.

## Live status report

Open the [Ecosystem Control Plane workflow](https://github.com/RFT-SIRM/Phi-Genesis/actions/workflows/ecosystem-control.yml). Each scheduled or manually triggered run publishes its report in the workflow summary and as downloadable artifacts.

The monitor runs every six hours and can also be started manually. It is read-only: it does not trigger tests in other repositories and does not alter their state.

## Registered projects

| Project | Scope | Actions |
|---|---|---|
| Phi-Genesis | Spectral computation and target-selection audit | [Runs](https://github.com/RFT-SIRM/Phi-Genesis/actions) |
| UltraCore-RFT | Research portal and coordination | [Runs](https://github.com/RFT-SIRM/UltraCore-RFT/actions) |
| Theory of Everything | Dissertation and higher-moment research | [Runs](https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/actions) |
| Evgeny Theorem | Lean 4 formalization | [Runs](https://github.com/RFT-SIRM/Evgeny-Theorem/actions) |
| Rift Network | Network engineering | [Runs](https://github.com/RFT-SIRM/Rift-Network/actions) |
| Rift-L1 Blockchain | Blockchain engineering | [Runs](https://github.com/RFT-SIRM/Rift-L1-Blockchain/actions) |
| Agave Rift Scheduler | Scheduler CI and fuzzing | [Runs](https://github.com/RFT-SIRM/agave-rift-scheduler/actions) |
| RFT-QPU-Sierpinski | Pre-experimental architecture | [Runs](https://github.com/RFT-SIRM/RFT-QPU-Sierpinski/actions) |
| RFT-Invariant-Battery | Exploratory energy-system model | [Runs](https://github.com/RFT-SIRM/RFT-Invariant-Battery/actions) |

## Status meanings

- **PASS:** only the latest reported workflow run completed successfully.
- **FAIL:** the latest reported workflow failed or timed out.
- **RUNNING:** the latest reported workflow is still in progress.
- **NOT RUN / NOT FOUND / API LIMITED / ERROR:** status is unavailable or incomplete; it is not a pass.

## Evidence boundary

The report is a snapshot of public Actions metadata, not a complete test audit or a guarantee that every workflow is green. It does not reproduce mathematical results, independently verify a scientific claim, or change the evidence status of the target indices `{1, 12, 17, 40}`.

For project-specific evidence, see [Verified Results](verified-results.md), [Selection Protocol](selection-protocol.md), and the [source repository](https://github.com/RFT-SIRM/Phi-Genesis).

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
