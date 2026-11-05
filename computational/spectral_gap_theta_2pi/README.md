# The θ = 2π spectral gap and the constant 1.30912892028081…

> **Status in one line.** For the explicit local-face operator `H = D + A_s` on the Sierpiński gasket,
> the bottom eigenvalue is bounded below by **1 for every refinement level** (Lean 4, no `sorry`),
> and numerically it **stabilizes at 1.30912892028081** from level 5 to level 8.
> The exact value and the convergence of the bottom eigenvalue to it are **not proved**.

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
| `Q` is the Gram matrix of a signed edge-incidence matrix, `Q = BᵀB`, hence positive semidefinite | `PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean`, commit `86d8d1e` (`sgSignedIncidenceMatrix`) | formalized, on `main` |
| Every real eigenvalue (with a nonzero real eigenvector) of the signed Laplacian is **≥ 1**, for every level `m` | same file, `sgSignedLaplacianMatrix_eigenvalue_ge_one` | formalized, on `main` |
| The gap cannot close at θ = 2π for the stated recursive face/sign model | `RESEARCH_LOG_2026-11-05.md`, lower-bound section | proved; uses only edge-disjoint triangular faces and vertex coverage |

The uniform bound `λ_min ≥ 1` is the rigorous content: the gap does **not** close as `m → ∞`.

## 3. What is observed numerically (not proved)

Bottom eigenvalue of `H` by refinement level (from `RESEARCH_LOG_2026-11-05.md`):

| level m | dim(H) | λ_min |
| ---: | ---: | ---: |
| 4 | 123 | 1.30912891862700 |
| 5 | 366 | 1.30912892028081 |
| 6 | 1,095 | 1.30912892028081 |
| 7 | 3,282 | 1.30912892028081 |
| 8 | 9,843 | 1.30912892028081 |

Successive differences: levels 2→3 about 1.1·10⁻², 3→4 about 5.8·10⁻⁵, 4→5 about 1.7·10⁻⁹, then
zero to 14 digits. The decay is consistent with super-exponential convergence, but three decreasing
steps followed by numerical stabilization is **evidence, not a proof**.

## 4. What is not claimed

- That `1.30912892028081…` is the exact limit, or a closed form for it. It is an observation.
- That the model is *the* external θ = 2π model. The cited external `sg.py`/`gap.py` sources were not
  present in the repository, so this identification is **conditional**.
- That this operator equals the pivot-zero all-hole-flux representative produced by the default
  `mobius.py` solver. It does not.
- That the constant is an analogue of π. π has a definition as a geometric ratio. For this number no
  such definition or theorem exists yet. It may be a useful invariant; that has to be shown.
- Any link to the vertex-order lemmas (`gasketVertexOrder_*`). Those are combinatorial and do not
  involve the spectrum.

## 5. Open problems

1. Prove that `λ_min(m)` converges, and identify the limit (closed form or recursion fixed point).
2. Explain why the bottom eigenvalue is constant to 14 digits from level 5. This suggests an exact
   eigenvector supported on a bounded patch, which would be provable on its own.
3. Close the conditional step: tie the local-face model to the external θ = 2π operator.

## 6. Reproduce

All numbers above are in `RESEARCH_LOG_2026-11-05.md` in this directory, with the method and the
exact combinatorial and edge-gauge audits (passing through level 10). Lean check:

```
lake build
```

and then `#print axioms` on `sgSignedLaplacianMatrix_eigenvalue_ge_one`.

## 7. Files

| Path | Content |
| --- | --- |
| `RESEARCH_LOG_2026-11-05.md` | derivation, audits, eigenvalue tables |
| `../../PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean` | Lean: signed Laplacian, Gram identification, `λ ≥ 1` |
