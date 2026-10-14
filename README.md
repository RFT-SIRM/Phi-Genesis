# Phi-Genesis: Spectral Core for Fractal Vacuum Substrate


[![Lab](https://img.shields.io/badge/Lab-Phi--Genesis-dc2626?style=for-the-badge)](https://github.com/RFT-SIRM/Phi-Genesis)
[![Python](https://img.shields.io/badge/Python-3.10%2B-3776AB?style=for-the-badge&logo=python&logoColor=white)](https://python.org)
[![License](https://img.shields.io/badge/License-MIT-eab308?style=for-the-badge)](https://opensource.org/licenses/MIT)
[![Visualization](https://img.shields.io/badge/Visualization-Live%20Demo-06b6d4?style=for-the-badge)](https://rft-sirm.github.io/Phi-Genesis/)



Reproducible spectral computations on the Sierpiński gasket (SG) and related structures. This is the computational backbone of the RFT (Reality Fractal Theory) research programme.

**Status (2026-10-14):** v2.0 — core mathematics numerically verified (computational evidence; not machine-checked). **No selection rule for the mass indices {1, 12, 17, 40} has been found.** Two pre-registered look-elsewhere tests (v1.0, v1.1) returned *no evidence*; see [Selection protocol status](#selection-protocol-status).

## Selection protocol status

The question tested: does any operator family on the Sierpiński gasket *select* the mass indices {1, 12, 17, 40} more often than chance, after correcting for the number of configurations tried (look-elsewhere effect)? Rules, null pools and thresholds were fixed and committed **before** each evaluation.

| Version | Rule | Configurations | Result | Commits |
|---|---|---|---|---|
| v1.0 | k = 12, window 60 | 75 | **no evidence** (p = 0.922 N-pot, 0.968 N-edge; threshold p <= 0.01). Post-hoc power check: the test could not have reached the threshold for any outcome, so this negative is uninformative. | c7e0c7f |
| v1.1 | k = 6, window 60 | 75 | **no evidence** (p = 0.966 N-pot, 0.997 N-edge). Max 2 of 4 targets in any configuration; index 40 selected by 0 of 75. This test *could* reach p <= 0.01, so the negative is informative for these 75 configurations. | d3605df, e9ffe15, 77e82ba, 743c415 |
| v1.2.1 | k = 8, window 60; SG x S^1 with spin structure (continuum circle, R^2 = 5^j) | 10 | **no evidence** (p = 0.953 N-circ, 0.926 N-circpot). Max 1 of 4 targets in any configuration (index 12); indices 1, 17, 40 never selected. Informative negative: the threshold was reachable. Not independent of F3 (lattice circle). | 1d9ed45, 1a71e0c, 3b7fa82 |

Cumulative configuration evaluations across all families tried: **193** (182 through v1.1, plus 1 exploratory rule check, plus 10 in v1.2.1; a lower bound, since the carpet search of ledger row 2, about 128 configurations at level 3 plus an unrecorded level-4 sweep, is not included) (full list in [`protocol_ledger.md`](protocol_ledger.md)).

**What this means for the results below.** The integer indices and the scale `A` in section 4 are not derived from any selection rule; the mass formula is a numerical match, not a prediction. Agreement should be read with the number of tried configurations in mind.

**Open blockers.** The top-quark index (about 1650) lies outside the window of 60 and cannot be selected by the current rule. Any Stage 2 needs a new operator family or rule, fixed in a new protocol version before it is evaluated.

Files: [`PREREGISTRATION.md`](PREREGISTRATION.md), [`PREREGISTRATION_v1.1_DRAFT.md`](PREREGISTRATION_v1.1_DRAFT.md), [`protocol_ledger.md`](protocol_ledger.md), `protocol_data/` (null pools, results, seeds), `phi_genesis/selection_protocol*.py`.

---

## Verified Results (numerical; reproducible via code)

### 1. Sierpiński gasket spectral theory
- **Spectral decimation ×5** — eigenvalues scale by factor ~5 between consecutive levels (exact for small λ).
- **Weyl law** — counting function N(λ) ~ λ^{d_s/2} with d_s/2 = ln(3)/ln(5) ≈ 0.6826. Finite-level bias ~3% at level 6, ~2.8% at level 8; levels 9-10 and window sensitivity: see Open Problem #2.
- **Log-periodic oscillations** — period ln(5), signature of decimation.
- **Fukushima–Shima gaps** — forbidden zones cluster at decimation fixed points λ ≈ 2.5 and λ ≈ 3.

### 2. Möbius (π-flux) boundary conditions
- Full π-flux through all holes **opens a mass gap**: first eigenvalue jumps from ~0.006 to ~0.46 at level 5.
- Partial twists also gap the spectrum.
- **Selection-rule test:** gap-selected indices follow the lacunary `3^k − 1` structure. The mass indices `{1, 12, 17, 40}` are **not** selected by gap rules.

### 3. Exhaustive twist search (32 configurations)
- All `2^5 = 32` generation-twist configurations at level 5 tested.
- **Max simultaneous hits on {1, 12, 17, 40}: 1 of 4.**
- **Index 40 never appears** as gap-selected under any configuration.
- This **closes the twist-by-generation family** as a candidate selection rule.

### 4. Integer mass formula
Using **integer** indices `n = {1, 12, 17, 40}` with a single scale `A = 104.63` MeV:

| Fermion | n | M_pred (MeV) | M_exp (MeV) | Error |
|---------|---|--------------|-------------|-------|
| μ | 1 | 104.63 | 105.658 | 0.97% |
| τ | 17 | 1778.71 | 1776.86 | 0.10% |
| c | 12 | 1255.56 | 1275.00 | 1.52% |
| b | 40 | 4185.20 | 4180.00 | 0.12% |
| **Mean** | | | | **0.68%** |

This beats the fitted non-integer values (0.87% mean error). The decimals in earlier versions were noise around integers.

### 5. Scale consistency audit
- Fitted scale `A = 104.63` MeV (from integer fit).
- Formula `A = v·α/Φ⁶` gives **100.13** MeV — 4.3% below fitted. Discrepancy confirmed.
- Relative spread of per-fermion implied scales: **0.58%**.

### 6. η-invariant claim — REJECTED
The RFT-String v8.7 claim that `η̄(0) = −4` for the boundary potential `V(i) = 0.5·(4y/√3 − 1)` is **not reproduced**:
- For the claimed potential: asymmetry = +1
- For random potential: −1
- For zero potential: −2
- Value −4 **never observed**. The asymmetry is an O(1) finite-size artifact, not a topological invariant.

### 7. Top-quark n_t inconsistency — NOT RESOLVED
The top quark is intentionally absent from the 4-fermion integer table above.
Reason (verified in `test_top_quark_consistency.py`): the historically
advertised `n_t = 1680 = 8·7#` was computed under an OLDER scale
(A ≈ 103.63 MeV), not the A = 104.63 MeV used everywhere else in this
section. Recomputing at the current A gives three genuinely different
candidates:

| Candidate | n_t | How it's obtained |
|---|---|---|
| Advertised ("8×7#") | 1680 | `v/(√2·A)` at the *old* A ≈ 103.63 |
| Formula, current A | 1664 | `v/(√2·A)` at A = 104.63 |
| Best integer fit, current A | 1654 | `round(m_top / A)` at A = 104.63 |

Using the advertised n_t = 1680 with the current A gives a top-quark
error of **1.55%** — more than double the 4-fermion mean (0.68%).
Including it would raise the reported mean to ~0.85%, back to the
level of the old fitted decimals the integer fit is presented as
improving on. No single n_t is asserted as correct here; the
inconsistency itself is the finding, guarded against regressing
silently by the three tests in `test_top_quark_consistency.py`.

### 8. Index-1 triviality caveat — affects the CORE result, not just carpet
Verified in `test_sg_index_triviality.py` on the actual SG graph (not
the abandoned carpet branch): under thousands of random on-site
potentials (unrelated to any specific flux/twist mechanism), index 1
appears in the gap-selected set **~95% of the time**, regardless of
what the potential is. For comparison: index 12 ~37%, index 17 ~22%,
index 40 ~3.4%.

This means the μ↔n=1 correspondence (section 4) and the "1 of 4" hit
reported for the exhaustive Möbius twist search (section 3) carry much
less evidential weight than they appear to at face value — index 1 is
close to a structural artifact of the ratio-based gap-selection rule
itself, not a signature of the π-flux mechanism specifically. An index
40 hit would be far more meaningful (only ~3.4% base rate) than an
index 1 hit (~95% base rate) — the four "hits" in this repo are not
equally strong evidence, and should not be reported as if they were.

### 9. Structural coincidence involving the index 40 — NOT evidence
On the untwisted SG the multiplicities of the special eigenvalues are, at levels 3-7: mult(3) = (3^(m-1)-3)/2, mult(5) = (3^(m-1)-1)/2, mult(6) = (3^m-3)/2 (checked at levels 3-6 in `test_sg_inertia.py`; levels 3-7 numerically). In particular mult(5) = 40 at level 5, and (3^k-1)/2 = 1, 4, 13, 40 contains two of the four mass indices {1, 12, 17, 40}. A random 4-subset of {1,...,40} contains at least two of {1, 4, 13, 40} with probability 4.3%. This is not evidence: the form (3^k-1)/2 was chosen after seeing the indices (a look-elsewhere effect over many possible integer forms); the repository's selection rule uses gap positions, not multiplicities (at level 5 the multiplicity-40 cluster occupies nonzero-eigenvalue positions 203-242); and the other two indices (12, 17) do not have this form. Recorded so that the coincidence is not later reported as support.

---

## Open Problems

### #1 — Selection rule for n_f (priority)
The formula `m = A·n` is numerically accurate, but `n` is not yet derived from spectral properties. We need a boundary condition or operator on SG × S¹ that selects `n ∈ {1, 12, 17, 40}` independently of experimental input.

**Tried (no evidence; 193 configuration evaluations, see [`protocol_ledger.md`](protocol_ledger.md)):**
- Z2 twists by generation (32 configurations)
- Scalar vertex potentials V(x) on SG and Dirichlet conditions at corners (pre-registered v1.0, v1.1)
- SG × S¹ with a lattice circle (v1.0, v1.1) and with a continuum circle and both spin structures (v1.2.1)
- Sierpiński carpet (branch abandoned, counts not recorded)

**Still untested:**
- Random dendrites, higher-genus or branched coverings of SG
- A derivation of the indices from an invariant of the operator (instead of a statistical search over families)

Any further family needs a new pre-registered protocol version, with a null-only power check, before it is evaluated.

### #2 — Finite-level convergence of d_s/2
Naive Weyl fit: ~2.8% error at level 8 (9843 vertices). Phase-averaged sliding windows can dip below 1%, but the result depends on window width and step — not yet a unique correction.

**Update (exact counts to level 10).** `phi_genesis/sg_inertia.py` counts the eigenvalues below any sigma exactly by Sylvester's law of inertia, with no eigensolver. It agrees with dense spectra at levels 5-6 (tests) and needs ~0.6 s and ~250 MB per count at level 9 (29,526 vertices) and ~700 MB at level 10 (88,575 vertices) on one CPU core. Findings:

- Fixed window sigma in [3e-3, 0.375] (3 log-periods, phase-averaged): deviation of the fitted exponent from ln3/ln5 is -2.19% (level 6), -0.61% (7), +0.07% (8), +0.32% (9), +0.41% (10).
- Window sensitivity (sigma in [2e-3, 0.45], windows of k log-periods sliding in steps of ln5/16), level 9: k=1 gives slopes 0.545...0.857 (mean +1.00%); k=2 gives 0.645...0.730 (mean +0.44%); k=3 gives 0.672...0.704 (mean +0.78%).
- Interpretation: the number of levels is no longer the bottleneck; the estimate is set by the window choice (log-periodic oscillation of order +-2-3% around the mean). The mean also drifts upward with level at a fixed window, consistent with the window top lying outside the asymptotic regime (not separately tested). The exponent d_s/2 = ln3/ln5 is known exactly from theory, so these numbers are consistency checks, not new information.
- Not tested: level 11 and above (fill-in memory is the expected limit, unverified).

**Path forward:** an analytical finite-size correction from decimation theory, or an estimator that is stable under window choice. More levels alone will not remove the window dependence.

### #3 — Light fermions
Electron, up, down, strange quarks not yet addressed. A fractal NJL mechanism is sketched but not implemented.

Note: with A = 104.63 MeV the integer formula `m = A·n` would need n ≈ 0.005 (electron), ≈ 0.02 (up), ≈ 0.04 (down) and ≈ 0.9 (strange) (approximate PDG masses), i.e. not integers ≥ 1. Light fermions therefore require a mechanism beyond the integer-index formula; any such mechanism brings its own parameters, which must be counted against the number of masses it is meant to explain.

---

## Repository Structure

```
phi_genesis/
  __init__.py                         — module exports
  sg_laplacian.py                     — SG graph, Laplacian, decimation, Weyl
  dirac_eta.py                        — Graph Dirac operator, η-invariant test
  mass_check.py                       — Scale consistency audit
  mobius.py                           — π-flux signed Laplacian (Z₂ cocycle)
  mobius_selection_search.py          — Exhaustive twist search (32 configs)
  fukushima_shima.py                  — Gap structure verification
  spectral_convergence.py           — Dense solver, Weyl fits, window sensitivity
  sg_inertia.py                     — Exact eigenvalue counts via inertia (levels 9-10, no eigensolver)
  test_honest.py                      — 5 core tests (~4s)
  test_mobius.py                      — 3 twist/integer tests (~0.1s)
  test_fukushima_shima.py             — 1 gap test (~1.6s)
  test_convergence_and_selection.py   — 4 deep tests (~13s, level 8 skipped in CI)
  test_sg_inertia.py                  — 4 fast tests (~1.2s) + nightly window sweep (levels 8-9)
```

---

## Quick Start

```bash
pip install numpy scipy
python -c "import phi_genesis; print('OK')"
```

### Run tests

```bash
# Fast suite (~6s)
python test_honest.py
python test_mobius.py
python test_fukushima_shima.py

# Deep suite (~13s, excludes level-8 dense solver)
python test_convergence_and_selection.py

# Level-8 dense solver manually (~60s, 9843 vertices)
python -c "from phi_genesis import dense_laplacian_spectrum; dense_laplacian_spectrum(8)"
```

---

## Key Numbers

| Quantity | Value | Source |
|----------|-------|--------|
| A (integer fit) | 104.63 MeV | Best fit to μ/τ/c/b with integer n |
| A (formula) | 100.13 MeV | v·α/Φ⁶ — 4.3% below fitted |
| d_s/2 (theory) | 0.6826 | ln(3)/ln(5) |
| d_s/2 (naive, level 6) | 0.7051 | 3.3% above theory |
| d_s/2 (naive, level 8) | 0.7019 | 2.8% above theory |
| Mean error (integer n, 4 fermions) | **0.68%** | Better than fitted decimals (0.87%) |
| Mean error (fitted n, 5 fermions) | 0.87% | Old non-integer values |
| η-asymmetry (claimed potential) | +1 | Not −4 |

---

## Roadmap

1. **Selection rule search** — tried so far: Z2 twists, scalar potentials, Dirichlet corners, SG × S¹ (lattice and continuum circle), carpet; no evidence after 193 configuration evaluations (see ledger). Next: only a derivation of the indices or a new family under a new pre-registered version (the target set was fixed after the fit, so look-elsewhere effects apply)
2. **Deeper levels** — levels 9-10 done via exact inertia counting, no GPU needed (see Open Problem #2); more levels do not remove the window dependence
3. **Light fermions** — implement fractal NJL integral (a toy at best: an NJL gap equation brings its own coupling and cutoff; parameters must be counted against the number of masses)
4. **Physical bridge** — connect A = 104.63 MeV to electroweak scale via RG (blocked: no Lagrangian or beta functions are defined in this repository, so there is nothing to run; a specified model is needed first)

---

## Scope: relation to Evgeny's Theorem

Nothing in the code or documentation of this repository uses [Evgeny's Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem), and no result here depends on it. That theorem is an exact trace-defect identity for a non-Abelian SU(2) connection on Sierpiński-gasket graphs; it is machine-checked in Lean 4 for every level m ≥ 1 (fourth moment, concrete operators). Phi-Genesis instead computes spectral properties of Abelian (Z₂, π-flux) signed Laplacians and a mass-index formula. The two differ in gauge group (Z₂ versus SU(2)), in observable (low-lying spectrum and gaps versus a fourth-moment trace defect), and in evidence (numerical versus formally proved).

Consequently the machine-checked status of Evgeny's Theorem does **not** transfer to any claim in this repository. Everything here is computational evidence (Level B in the [Unified Foundations verification policy](https://github.com/RFT-SIRM/Unified-Foundations-Mathematics-Physics/blob/main/VERIFICATION_POLICY.md)) unless stated otherwise, and the mass formula `m = A·n` still lacks an independent selection rule.

---

## Citation

If you use this code, please cite the RFT research programme and acknowledge that the mass formula `m = A·n` currently lacks an independent selection rule.

---

*All computations are reproducible. All claims are tested against code. No black boxes.*
