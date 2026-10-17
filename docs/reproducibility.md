# Reproducibility and Computational Workflow

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


The repository's source code, tests, fixed-seed protocol data and versioned records are the primary reproducibility artifacts. This guide summarizes the commands in the project README; use a clean local clone and follow the cautions below.

## Environment

The project uses Python with NumPy and SciPy for numerical work.

```bash
pip install numpy scipy
python -c "import phi_genesis; print('OK')"
```

For editable installation and tests:

```bash
pip install -e . pytest
pytest -q -m "not nightly"
```

The README reports that the fast suite can take roughly 2–3 minutes on one CPU core, with the level-8 test dominating. Nightly tests are excluded by this command.

## Reproduce protocol v1.2.1

```bash
python -m phi_genesis.selection_protocol_v121 stepA
python -m phi_genesis.selection_protocol_v121 stepB
```

- `stepA` regenerates the null pools using seeds fixed in the code; the README estimates about 15 minutes.
- `stepB` runs the evaluation and should be compared with `protocol_data/results_v1_2_1.json`.
- **Caution:** `stepA` rewrites `protocol_data/null_pools_v1_2_1.json`. If you want to preserve the committed file exactly, perform the reproduction on a separate working copy.

## Reproduce Open Problem #2 estimator studies

```bash
python protocol_data/op2_window_bias.py table
python protocol_data/op2_window_bias.py sliding
python protocol_data/op2_chord_estimator.py 8 9
```

The window-bias script uses the cached numerical inertia counts documented by the project. The chord-estimator command compares levels 8 and 9 for the documented estimator.

## What to record

For a reproducible report, include:

- Git commit SHA and Python / NumPy / SciPy versions;
- exact command and test selection;
- graph level, operator convention, boundary condition and numerical tolerance;
- protocol version, random seeds and null ensemble;
- whether an output was regenerated or read from committed data;
- any deviation from preregistered settings.

A passing test suite validates the tested code paths, not every scientific interpretation in the repository. Numerical results should always be reported with their level, estimator, parameter range and known limitations.

## Source artifacts

- [Repository and test suite](https://github.com/RFT-SIRM/Phi-Genesis)
- [Selection protocol code and data](https://github.com/RFT-SIRM/Phi-Genesis/tree/main/protocol_data)
- [Methodology](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md)

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
