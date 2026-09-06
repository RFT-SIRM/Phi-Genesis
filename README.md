# Phi-Genesis: Spectral Core for Fractal Vacuum Substrate


[![Lab](https://img.shields.io/badge/Lab-Phi--Genesis-dc2626?style=for-the-badge)](https://github.com/RFT-SIRM/Phi-Genesis)
[![Python](https://img.shields.io/badge/Python-3.10%2B-3776AB?style=for-the-badge&logo=python&logoColor=white)](https://python.org)
[![License](https://img.shields.io/badge/License-MIT-eab308?style=for-the-badge)](https://opensource.org/licenses/MIT)
[![Visualization](https://img.shields.io/badge/Visualization-Live%20Demo-06b6d4?style=for-the-badge)](https://rft-sirm.github.io/Phi-Genesis/)



Reproducible spectral computations on the Sierpiński gasket (SG) and related structures. This is the computational backbone of the RFT (Reality Fractal Theory) research programme.

**Status:** v2.0 — all core mathematics verified; selection rule for fermion masses remains an open problem.

---

## Verified Results (reproducible via code)

### 1. Sierpiński gasket spectral theory
- **Spectral decimation ×5** — eigenvalues scale by factor ~5 between consecutive levels (exact for small λ).
- **Weyl law** — counting function N(λ) ~ λ^{d_s/2} with d_s/2 = ln(3)/ln(5) ≈ 0.6826. Finite-level bias ~3% at level 6, ~2.8% at level 8.
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
- Formula `A = v·α/Φ⁶` gives **100.13** MeV — 3.4% below fitted. Discrepancy confirmed.
- Relative spread of per-fermion implied scales: **0.58%**.

### 6. η-invariant claim — REJECTED
The RFT-String v8.7 claim that `η̄(0) = −4` for the boundary potential `V(i) = 0.5·(4y/√3 − 1)` is **not reproduced**:
- For the claimed potential: asymmetry = +1
- For random potential: −1
- For zero potential: −2
- Value −4 **never observed**. The asymmetry is an O(1) finite-size artifact, not a topological invariant.

---

## Open Problems

### #1 — Selection rule for n_f (priority)
The formula `m = A·n` is numerically accurate, but `n` is not yet derived from spectral properties. We need a boundary condition or operator on SG × S¹ that selects `n ∈ {1, 12, 17, 40}` independently of experimental input.

**Untested families:**
- Scalar vertex potentials V(x) on SG
- Mixed boundary conditions (Dirichlet on some holes, Neumann on others)
- Other fractals: Sierpiński carpet, random dendrites
- SG × S¹ with different S¹ topologies and fluxes
- Higher-genus or branched coverings of SG

### #2 — Finite-level convergence of d_s/2
Naive Weyl fit: ~2.8% error at level 8 (9843 vertices). Phase-averaged sliding windows can dip below 1%, but the result depends on window width and step — not yet a unique correction.

**Path forward:** level 9+ (needs optimization), or analytical finite-size correction from decimation theory.

### #3 — Light fermions
Electron, up, down, strange quarks not yet addressed. A fractal NJL mechanism is sketched but not implemented.

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
  test_honest.py                      — 5 core tests (~4s)
  test_mobius.py                      — 3 twist/integer tests (~0.1s)
  test_fukushima_shima.py             — 1 gap test (~1.6s)
  test_convergence_and_selection.py   — 4 deep tests (~13s, level 8 skipped in CI)
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
| A (formula) | 100.13 MeV | v·α/Φ⁶ — 3.4% below fitted |
| d_s/2 (theory) | 0.6826 | ln(3)/ln(5) |
| d_s/2 (naive, level 6) | 0.7051 | 3.3% above theory |
| d_s/2 (naive, level 8) | 0.7019 | 2.8% above theory |
| Mean error (integer n, 4 fermions) | **0.68%** | Better than fitted decimals (0.87%) |
| Mean error (fitted n, 5 fermions) | 0.87% | Old non-integer values |
| η-asymmetry (claimed potential) | +1 | Not −4 |

---

## Roadmap

1. **Selection rule search** — scalar potentials, mixed BCs, other fractals, twisted S¹
2. **Deeper levels** — level 9+ via sparse optimization or GPU
3. **Light fermions** — implement fractal NJL integral
4. **Physical bridge** — connect A = 104.63 MeV to electroweak scale via RG

---

## Citation

If you use this code, please cite the RFT research programme and acknowledge that the mass formula `m = A·n` currently lacks an independent selection rule.

---

*All computations are reproducible. All claims are tested against code. No black boxes.*
