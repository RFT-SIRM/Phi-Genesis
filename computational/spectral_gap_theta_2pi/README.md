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
that the bottom eigenvalue is constant from level 5 onward. Direct high-precision quotient calculations resolve the `A1` bottom through level 9 and the `E` mode through level 8. A separate outward-rounded interval/Schur-inertia certificate now verifies, for every finite level 1–12, that the `A1` root is the simple global minimum and the `E` root is the next eigenvalue with multiplicity two. The limiting value and convergence law as the level tends to infinity remain open. The `S3` symmetry-sector decomposition has also been checked against
the complete spectrum at levels 2–5.

Run the reproducible calculation from the repository root:

```bash
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/high_precision_bottom.py
```

The computation uses 80 decimal digits in `mpmath`. Float64 is used only to seed the initial
three-dimensional low-eigenspace; block inverse iteration for `(H-I)^{-1}`, preconditioned conjugate
gradients, orthogonalization, and the final 3×3 Rayleigh–Ritz diagonalization are carried out in
multiple precision. The residual diagnostics are numerical, not interval-arithmetic certificates.

| level m | dim(H) | computed bottom candidate (high precision) |
| ---: | ---: | ---: |
| 2 | 15 | 1.2984378812835756567558911626890933677398… |
| 3 | 42 | 1.3090710652556068404036933845248248253260… |
| 4 | 123 | 1.3091289186270032373372269265507617266049… |
| 5 | 366 | 1.3091289202808134205376249464114593830015… |
| 6 | 1,095 | 1.3091289202808134218886230881708101876508… |
| 7 | 3,282 | 1.3091289202808134218886230881708101885523242511173263434335359844526816970029… |
| 8 | 9,843 | 1.3091289202808134218886230881708101885523242511173263434335359844526816974043999830777949027911712… |
| 9 | 29,526 | 1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341956895023566459152736… |

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
| 6→7 | 9.01556448009307575101·10⁻³⁷ | 0.4939504899001989666 |
| 7→8 | 4.01484948291304833402·10⁻⁷³ | 0.4939504899001989529 |
| 8→9 | 7.96199603289170721200·10⁻¹⁴⁶ | 0.49395048990019895288 |

The six ratios in the spectral table extend through `8→9`. The exact Schur recursion below extends the same continued `A1` boundary-root sequence through levels 10–12; the ratios `δ_10/δ_9²`, `δ_11/δ_10²`, and `δ_12/δ_11²` agree near `0.49395048990019895285628827965354…`. This is strong numerical evidence and a structural explanation candidate, but not yet a theorem: convergence of the root sequence and uniform control of the derivative have not been proved. Extrapolations remain conditional and carry no certified error bound.

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

At level 7 the sector dimensions are `dim(A1)=551`, `dim(A2)=543`, and `dim(E)=1,094`,
so `551 + 543 + 2·1,094 = 3,282`. The `A1` bottom is
`1.3091289202808134218886230881708101885523242511173263434335359844526816970029…`.
The bottom of one `E` copy is
`1.3091289202808134218886230881708101885523242511173263434335359844526816976051…`.
Their difference is approximately `6.02227422437·10⁻⁷³`; the high-precision residuals are
`2.18·10⁻⁹⁴` in `A1` and `1.82·10⁻⁷⁷` in `E`. Thus the numerical resolution is below
the observed splitting. The next eigenvalues in both sectors are near 2, giving a gap of about
`0.69087108` above the bottom mode.

At level 8, `dim(A1)=1,645`, `dim(A2)=1,636`, and `dim(E)=3,281`, so
`1,645 + 1,636 + 2·3,281 = 9,843`. The high-precision `A1` bottom is
`1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341948933027533567445524…`,
with residual `1.04·10⁻⁹⁷`. The bottom of one `E` copy is
`1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341960876021582905006341…`,
with residual `9.45·10⁻⁹⁸`. Their splitting is approximately
`1.1942994049337560817·10⁻¹⁴⁵`. The float64 sector spectrum places the next modes near 2,
about `0.69087108` above the bottom. Using this numerically observed separation, the residual-squared
Rayleigh error estimates are around `10⁻¹⁹⁴`, much smaller than the splitting; these are not
interval certificates.

At level 9, `dim(A1)=4,926` in a graph of `29,526` vertices. Its bottom is
`1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341956895023566459152736…`,
with residual `8.11·10⁻⁹⁸`. The `A2` sector at level 9 has not been independently diagonalized as a matrix, but the interval/inertia certificate below proves that all modes outside the `A1` ground state and the `E` doublet lie above the certified `E` root.

The `E`-to-`A1` splitting divided by `δ_m²` is approximately `0.74092573485029842928443241948031142231612216498…` from level 7 onward. Levels 7–8 come from high-precision sector matrices; levels 9–12 are Schur boundary roots now enclosed by the finite-level interval/inertia certificate. The level-9, 10, 11, and 12 splittings are approximately `4.6969787274470149·10⁻²⁹¹`, `7.2648951037178442·10⁻⁵⁸²`, `1.7380043433370844·10⁻¹¹⁶³`, and `9.9470402734076902·10⁻²³²⁷`, respectively. The level-12 ratio `(E_12-A1_12)/δ_12²` is `0.74092573485029842928443241948031142231612216498…`.


### Exact A1/E boundary Schur recursion

Let \(S_m(\lambda)\) be the 3×3 Schur complement of \(Q_m-\lambda I\) after eliminating every non-corner vertex. By \(S_3\) symmetry it has the form

\[
S_m(\lambda)=(a_m(\lambda)-b_m(\lambda))I_3+b_m(\lambda)J_3.
\]

At level zero, \((a_0,b_0)=(2-\lambda,1)\). To pass from level \(m\) to \(m+1\), glue three level-\(m\) cells along their three midpoint vertices. Each midpoint belongs to two child boundaries, so the assembled boundary matrix receives a correction \(+\lambda\) on each midpoint diagonal: the child Schur complements each included a \(-\lambda\) term, whereas the global matrix contains it only once. With \(T=J_3-I_3\) and \(c_m=2a_m+\lambda-b_m\), eliminating the midpoints gives the exact rational recursion

\[
\begin{aligned}
a_{m+1}&=a_m-\frac{2b_m^2(c_m+b_m)}{c_m(c_m+3b_m)},\\
b_{m+1}&=-\frac{b_m^2(c_m-b_m)}{c_m(c_m+3b_m)}.
\end{aligned}
\]

Away from poles of the eliminated interior block, the symmetric-boundary eigenvalue condition is \(a_m(\lambda)+2b_m(\lambda)=0\). On the two-dimensional boundary subspace orthogonal to \((1,1,1)\), the all-ones matrix \(J_3\) vanishes, so the standard E-boundary eigenvalue is \(a_m(\lambda)-b_m(\lambda)\); its root satisfies \(a_m-b_m=0\). The script continues both low boundary roots from levels 1 and 2 by high-precision Newton steps. The finite-level algebraic recursion is exact; identifying either continued root as the lowest mode at every large level remains a separate spectral task.

The recursion was compared with direct dense Schur complements of the graph matrices at levels 0–4 and three regular spectral parameters (1.234, 1.309, 1.411). The maximum float64 discrepancy was below 1.4·10⁻¹⁶. Forward-mode derivatives were also compared with mpmath.diff through level 6.

The continued boundary roots give:

| Transition | Schur-root increment |
| --- | ---: |
| 9→10 | 3.13131915163134327525017302593668834473·10⁻²⁹¹ |
| 10→11 | 4.84326340247856280976678937076391662801·10⁻⁵⁸² |
| 11→12 | 1.15866956222472296571000231092429262929·10⁻¹¹⁶³ |

The three corresponding quadratic ratios agree to about 48 significant digits:
0.493950489900198952856288279653540948210748109986…

The standard E-boundary channel is therefore obtained from the same recursion, not from a second matrix construction. Its level-m root minus the A1 root gives:

| Level m | E-boundary root − A1-boundary root |
| --- | ---: |
| 9 | 4.69697872744701491287525953890503251710·10⁻²⁹¹ |
| 10 | 7.26489510371784421465018405614587494201·10⁻⁵⁸² |
| 11 | 1.73800434333708444856500346638643894393·10⁻¹¹⁶³ |

For levels 9–11 the ratio of this splitting to the square of the A1 increment is stable near
0.74092573485029842928443241948031142231612216498… . Moreover, the ratio
\((E_m-A_{1,m})/\delta_{m+1}\) is numerically 3/2 through levels 7–10, with the finite-level deviation shrinking from about 10⁻¹⁴⁴ to about 10⁻¹¹⁶¹.

This 3/2 relation has a conditional derivation. At an A1 root, (a_m=-2b_m), so the E characteristic evaluated there is (a_m-b_m=-3b_m). The next A1 characteristic evaluated at the same point is
\[
f_{m+1}(\lambda_m)=-2b_m\frac{c_m+5b_m}{c_m+3b_m}\sim-2b_m.
\]
If the derivatives of these two characteristics approach the same nonzero limit, their root corrections are asymptotic to (-3b_m/L) and (-2b_m/L), respectively. Hence
\[
E_m-A_{1,m}\sim\frac{3}{2}\,(A_{1,m+1}-A_{1,m}).
\]
Combining this with the quadratic A1 increment law predicts that the E-splitting coefficient is 3/2 times the A1 coefficient. The shared derivative limit and convergence assumptions are not proved yet.

There is a useful conditional explanation for this coefficient. At a level-m root, \(a_m=-2b_m\). The recursion then gives
\[
f_{m+1}(\lambda_m)=-2b_m\frac{c_m+5b_m}{c_m+3b_m},
\qquad
\frac{b_{m+1}(\lambda_m)}{b_m(\lambda_m)^2}
\longrightarrow -\frac{1}{\lambda_\infty}
\]
provided \(\lambda_m\to\lambda_\infty\) and \(b_m\to0\). If additionally
\(f'_{m+1}(\lambda_m)\to L\ne0\), Taylor expansion predicts
\[
\frac{\delta_{m+1}}{\delta_m^2}
\longrightarrow
\frac{1/\lambda_\infty}{-2/L}.
\]
Numerically, \(-2/L\approx1.54644387367797039232151350963469\ldots\), while
\(1/\lambda_\infty\approx0.76386670900639485955066454013148\ldots\).
This gives the observed coefficient near 0.493950489900198952856288… The limit and derivative hypotheses are not yet proved, so this is a route toward a proof, not the proof itself.

Reproduce the level-12 Schur calculation with:

~~~bash
python computational/spectral_gap_theta_2pi/schur_decimation.py --sector A1 --max-level 12 --dps 1250
python computational/spectral_gap_theta_2pi/schur_decimation.py --sector E --max-level 11 --dps 1250
~~~


### Finite-level interval/inertia certificate (levels 1–12)

The boundary matrix is `S_m=(a_m-b_m)I+b_mJ`, so its three eigenvalues are `f_m=a_m+2b_m` in the A1 channel and `g_m=a_m-b_m` twice in the E channel. The midpoint pivot at each three-cell gluing step is `C_k=c_kI+b_kJ`, with eigenvalues `c_k` (twice) and `c_k+3b_k` (once).

The checker brackets every A1 and E boundary root at 2,450 decimal digits with radius `10^-2390`. The approximate root only chooses the bracket: the checker independently verifies opposite endpoint signs and a strictly negative derivative throughout the interval. It also verifies `b_m<0` and that both midpoint-pivot eigenvalues are strictly positive at every elimination step. The smallest lower bound for any midpoint-pivot eigenvalue across all 24 certificates (A1 and E, levels 1–12) is greater than `1.151628330238438…`.

These signs give an inertia proof for each finite level. At an A1 root, `f_m=0` and `g_m=-3b_m>0`, so the boundary Schur complement is positive semidefinite with a one-dimensional kernel. All eliminated interior blocks are positive definite, hence `Q_m-λI` is positive semidefinite with a simple kernel: this root is the global minimum. At an E root, `g_m=0` twice and `f_m=3b_m<0`, so the full shifted matrix has exactly one negative eigenvalue and a two-dimensional kernel. Thus the E root is the second eigenvalue with multiplicity two, and all remaining modes (including A2) are above it. The A1 and E root brackets are strictly ordered and disjoint at every level 1–12.

This is a reproducible finite-level computer-assisted interval/inertia certificate, not a Lean-kernel theorem and not an infinite-level convergence proof. Run:

~~~bash
python computational/spectral_gap_theta_2pi/schur_inertia_certificate.py --max-level 12 --dps 2450 --radius-digits 2390
pytest -q test_spectral_schur_inertia.py
~~~

## 4. What is not claimed

- That `1.309128920280813421889…` is the exact limit, or a closed form for it. It is a conditional numerical extrapolation.
- That the quadratic correction law holds for all levels. The exact finite-level Schur recursion explains the observed asymptotic mechanism conditionally, but convergence and the derivative limit still need proof.
- That the local-face model is *the* external θ = 2π model. The cited external `sg.py`/`gap.py` sources were not present in the repository, so this identification is **conditional**.
- That this operator equals the pivot-zero all-hole-flux representative produced by the default `mobius.py` solver. It does not.
- That the constant is an analogue of π. No such definition or theorem exists yet.
- Any link to the vertex-order lemmas (`gasketVertexOrder_*`). Those are combinatorial and do not involve the spectrum.

## 5. Open problems

1. Prove that the certified finite-level `λ_min(m)` sequence converges, and identify its limit (closed form or recursion fixed point).
2. Explain the corner concentration and derive a controlled description of the nonzero tails. The numerical
   evidence rules out the earlier *compactly supported eigenvector on a bounded patch* explanation:
   thresholded support grows as the threshold is tightened, and the bottom eigenvalue is not exactly
   constant between levels 4 and 5.
3. Prove or disprove the apparent quadratic correction law `δ_(m+1) ≈ c·δ_m²` for all levels; finite-level ratios and the Schur mechanism are now known, but the limiting derivative hypotheses remain open.
4. Close the conditional step: tie the local-face model to the external θ = 2π operator.

## 6. Reproduce

From the repository root:

```bash
python -m pip install -e .
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/audit_triangle_gauge.py --max-level 10
python computational/spectral_gap_theta_2pi/high_precision_bottom.py
python computational/spectral_gap_theta_2pi/schur_decimation.py --sector A1 --max-level 12 --dps 1250
python computational/spectral_gap_theta_2pi/schur_decimation.py --sector E --max-level 12 --dps 1250
python computational/spectral_gap_theta_2pi/schur_inertia_certificate.py --max-level 12 --dps 2450 --radius-digits 2390
pytest -q test_spectral_gap_high_precision.py test_spectral_schur_decimation.py test_spectral_schur_inertia.py
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
| `symmetry_sector_bottom.py` | high-precision `A1`, `A2`, and `E` symmetry-sector calculations, including sparse-LU/multiprecision refinement |
| `schur_decimation.py` | exact rational three-corner Schur recursion and high-precision `A1`/`E` boundary-root continuation |
| `schur_inertia_certificate.py` | outward-rounded Decimal interval checks and finite-level Schur/inertia certificates for the ground state and first E doublet |
| `audit_triangle_gauge.py` | exact combinatorial, gauge, graph, and sparse spectral audits |
| `../../PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean` | Lean: signed Laplacian, Gram identification, and `λ ≥ 1` |
