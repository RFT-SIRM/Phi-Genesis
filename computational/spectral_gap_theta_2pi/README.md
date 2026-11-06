# The θ = 2π spectral gap and the limiting bottom eigenvalue

> **Status in one line.** For the explicit local-face operator `H = D + A_s` on the Sierpiński gasket,
> the bottom eigenvalue is bounded below by **1 for every refinement level** (Lean 4, no `sorry`).
> Finite-level computations show very rapid convergence near **1.3091289202808134…**.
> The limiting value, convergence theorem, and exact characterization remain **open**.

This directory is a spectral-gap workstream. It is **separate** from the scalar canonical GF(2) H10
recurrence in `computational/higher_moments_z2` and from the vertex-order formalization in
`PhiGenesis/H10`. Nothing here depends on those results and nothing there depends on this one.

---

## 1. The object

At the central twist angle **θ = 2π** the phase on a flux edge is the pure sign **−1**. The SU(2)
operator is then gauge-equivalent to the **signless Laplacian**

$$
Q \;=\; D + A_s ,
$$

where `D` is the degree matrix and `A_s` is the adjacency matrix carrying the local-face signing.
The project audit reports gauge-equivalence error `0.00e+00` at levels 1–5.

Every triangular face of the gasket then carries sign product **−1** (an odd, frustrated cycle).
Frustration is what keeps `Q` away from singularity: a signless Laplacian of a connected graph with no
balanced signing has trivial kernel.

## 2. What is proved (Lean 4)

| Statement | Where | Status |
| --- | --- | --- |
| `Q` is the Gram matrix of a signed edge-incidence matrix, `Q = BᵀB`, hence positive semidefinite | `PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean`, theorem `sgSignedLaplacianMatrix_eq_incidenceGram` | formalized, on `main` |
| Every real eigenvalue (with a nonzero real eigenvector) of the signed Laplacian is **≥ 1**, for every level `m` | same file, `sgSignedLaplacianMatrix_eigenvalue_ge_one` | formalized, on `main` |
| The gap cannot close for the stated recursive face/sign model | `RESEARCH_LOG_2026-11-05.md`, lower-bound section | proved; uses edge-disjoint triangular faces and vertex coverage |

The uniform bound `λ_min ≥ 1` is the rigorous content: the gap does **not** close as `m → ∞`.

## 3. What is observed numerically (not proved)

The earlier 14-digit plateau was caused by ordinary floating-point resolution and did **not** establish
that the bottom eigenvalue is constant from level 5 onward. High-precision calculations now resolve
the bottom eigenvalue through level 6 and independently separate the symmetry sectors of the graph's
S3 action.

Run the reproducible calculation from the repository root:

```bash
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/high_precision_bottom.py
```

The computation uses 80 decimal digits in `mpmath`. Float64 is used only to seed the initial
three-dimensional low-eigenspace; block inverse iteration for `(H-I)^{-1}`, preconditioned conjugate
gradients, orthogonalization, and the final 3×3 Rayleigh–Ritz diagonalization are carried out in
multiple precision. The residual diagnostics are numerical, not interval-arithmetic certificates.

| level m | dim(H) | λ_min (high-precision Rayleigh–Ritz) |
| ---: | ---: | ---: |
| 2 | 15 | 1.2984378812835756567558911626890933677398… |
| 3 | 42 | 1.3090710652556068404036933845248248253260… |
| 4 | 123 | 1.3091289186270032373372269265507617266049… |
| 5 | 366 | 1.3091289202808134205376249464114593830015… |
| 6 | 1,095 | 1.3091289202808134218886230881708101876508… |

At level 5 the next two eigenvalues form a near-degenerate pair at approximately
`1.309128920280813422564122159050485604429…`. Their separation from the bottom eigenvalue
is about `2.0264972·10⁻¹⁸`. This explains why a short single-vector inverse iteration can fail to
resolve the bottom mode: the three lowest eigenvalues are exceptionally close.

The positive increments `δ_m = λ_m − λ_(m−1)` and their quadratic ratios are:

| Transition | δ_m | δ_m / δ_(m−1)² |
| --- | ---: | ---: |
| 2→3 | 1.06331839720311836478·10⁻² | — |
| 3→4 | 5.78533713963969335335·10⁻⁵ | 0.5116842114039808057 |
| 4→5 | 1.65381018320039801986·10⁻⁹ | 0.4941153170828634048 |
| 5→6 | 1.35099814175935080465·10⁻¹⁸ | 0.4939504986563758755 |

The three successive ratios are now consistent with a quadratic correction law with coefficient near
`0.494`, but this remains an empirical pattern. Using only the latest ratio gives the conditional
prediction `δ_7 ≈ 9.01556463991·10⁻³⁷` and the conditional limit estimate
`1.3091289202808134218886230881708101885523…`. This is an empirical extrapolation, not a theorem
or a certified error bound. The convergence law and the limiting value remain open.

The observed eigenvectors are concentrated near the three corners, but they do not have compact
support: the apparent support depends on the numerical threshold used to display small components.
The finite-patch exact-eigenvector explanation is therefore not supported by these computations.


### Symmetry-sector audit (`S3`)

The graph's barycentric-coordinate permutations act by `S3`. The vertex representation decomposes as
`A1 ⊕ A2 ⊕ 2E`: the fully symmetric sector, the alternating sector, and two copies of the
two-dimensional standard representation. Independently assembled quotient matrices were compared
against the complete dense spectrum at levels 2–5. Their dimensions sum to the full graph dimensions,
and the sorted union of the sector spectra agrees with the full spectrum to at most
`1.6·10⁻¹⁴` in float64.

At level 6 the sector dimensions are `dim(A1)=186`, `dim(A2)=179`, and `dim(E)=365`,
so `186 + 179 + 2·365 = 1,095`. The bottom of `A1` is
`1.3091289202808134218886230881708101876508…`, while the bottom of one `E` copy is
`1.3091289202808134218886230881708101890031…`. Their splitting is
`1.3523346720·10⁻³⁶`. The bottom of `A2` is 2 in the computed quotient (high-precision
inverse-iteration residual `6.81·10⁻²⁸`). Thus the global bottom is in `A1`; the `E` sector
supplies the extremely close near-degenerate pair. Residuals are numerical diagnostics, not
interval certificates.

## 4. What is not claimed

- That `1.309128920280813421889…` is the exact limit, or a closed form for it. It is a conditional numerical extrapolation.
- That the quadratic correction law holds for all levels. Only two successive ratios are currently available.
- That the local-face model is *the* external θ = 2π model. The cited external `sg.py`/`gap.py` sources were not present in the repository, so this identification is **conditional**.
- That this operator equals the pivot-zero all-hole-flux representative produced by the default `mobius.py` solver. It does not.
- That the constant is an analogue of π. No such definition or theorem exists yet.
- Any link to the vertex-order lemmas (`gasketVertexOrder_*`). Those are combinatorial and do not involve the spectrum.

## 5. Open problems

1. Prove that `λ_min(m)` converges, and identify its limit (closed form or recursion fixed point).
2. Explain the corner concentration and derive a controlled description of the nonzero tails. The numerical
   evidence rules out the earlier *compactly supported eigenvector on a bounded patch* explanation:
   thresholded support grows as the threshold is tightened, and the bottom eigenvalue is not exactly
   constant between levels 4 and 5.
3. Prove or disprove the apparent quadratic correction law `δ_(m+1) ≈ c·δ_m²` beyond the two observed ratios.
4. Close the conditional step: tie the local-face model to the external θ = 2π operator.

## 6. Reproduce

From the repository root:

```bash
python -m pip install -e .
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/audit_triangle_gauge.py --max-level 10
python computational/spectral_gap_theta_2pi/high_precision_bottom.py
pytest -q test_spectral_gap_high_precision.py
lake build
```

The exact combinatorial and edge-gauge audit passes through level 10. The high-precision script
reproduces the finite-level values and prints its residual diagnostics. For the Lean result, run
`#print axioms PhiGenesis.SpectralGap.sgSignedLaplacianMatrix_eigenvalue_ge_one`.

## 7. Files

| Path | Content |
| --- | --- |
| `RESEARCH_LOG_2026-11-05.md` | derivation, audits, earlier eigenvalue tables, and evidence boundary |
| `high_precision_bottom.py` | high-precision three-vector spectral-cluster refinement |
| `symmetry_sector_bottom.py` | high-precision `A1`, `A2`, and `E` symmetry-sector calculations |
| `audit_triangle_gauge.py` | exact combinatorial, gauge, graph, and sparse spectral audits |
| `../../PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean` | Lean: signed Laplacian, Gram identification, and `λ ≥ 1` |
