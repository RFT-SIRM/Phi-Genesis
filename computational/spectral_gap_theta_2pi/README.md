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

At the central twist angle **θ = 2π**, the connection link variable is the pure sign **−1**. To keep the edge-sign conventions distinct, write the connection sign as `U_uv=-s_uv`, where the local-face signed-adjacency convention used in `H = D + A_s` has `s_ab=+1` on the first (horizontal) edge of each ordered upward face and `s_ac=s_bc=-1` on the other two edges.

Thus every elementary face has `s_ab s_ac s_bc = +1`, while the connection holonomy is `U_ab U_ac U_bc = -1`. The signed adjacency `A_s` is therefore a vertex-gauge transform of the ordinary adjacency `A`: with `ε(i,j)=(-1)^j`, one has `s_uv=ε(u)ε(v)` on every edge. Consequently

$$
H = D + A_s = G(D+A)G, \qquad G=\operatorname{diag}(ε),
$$

so `H` is exactly gauge-equivalent to the **ordinary signless graph Laplacian** `Q = D + A`. The product +1 belongs to the signed-adjacency convention `s`; the product −1 belongs to the connection convention `U=-s`. They are not contradictory.

The gasket graph contains triangular cycles and is non-bipartite, so its ordinary signless Laplacian has trivial kernel. The project audit reports gauge-equivalence error `0.00e+00` at levels 1–5.

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

A focused, independent scalar Schur-root computation is documented in [HIGH_PRECISION_2026-11-06.md](HIGH_PRECISION_2026-11-06.md), with runnable source [schur_bottom_eigenvalue.py](schur_bottom_eigenvalue.py). It reproduces the A1 bottom through level 9 and resolves the A1/E splitting. This corrected note **supersedes the erroneous high-precision conclusions merged in PR #12**: the earlier collapse and non-constant ratio came from Rayleigh quotients of double-precision vectors mixing the nearly degenerate A1 and E channels. The corrected data support a stable quadratic ratio numerically; they do not prove convergence or a limiting law.


Run the reproducible calculation from the repository root:

```bash
python -m pip install mpmath
python computational/spectral_gap_theta_2pi/high_precision_bottom.py
python computational/spectral_gap_theta_2pi/schur_bottom_eigenvalue.py
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
If the derivatives of these two characteristics approach the same nonzero limit, their root corrections are asymptotic to (3b_m/L) and (2b_m/L), respectively. Hence
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
python computational/spectral_gap_theta_2pi/schur_derivative_certificate.py --max-level 14 --start-level 5 --dps 10000 --radius-digits 9400
pytest -q test_spectral_schur_inertia.py
~~~

### A1 bootstrap-window interval experiment (levels 6–101)

A separate finite experiment is implemented in `schur_bootstrap_box_iv.py`. It starts from a
260-digit scalar candidate for the level-6 A1 root, then fixes one asymmetric parameter interval
`[lambda_6 - 10^-140, lambda_6 + 1.1·10^-36]` and propagates the exact Schur recursion over that
same interval through level 101 using outward-rounded `mpmath.iv` arithmetic at 180 digits.

For every level 6–101, the run checks opposite signs of the A1 characteristic at the two fixed
endpoints, a strictly negative A1 derivative throughout the interval, the proposed bootstrap
ranges for `a,b` and their first two derivatives, and positivity of every midpoint-pivot interval
encountered in the recursion. Thus each finite-level A1 characteristic has exactly one root in
the common interval. The minimum lower endpoint among the current midpoint-pivot eigenvalue
intervals is approximately `1.30912892028081342188862308817081018318…`.

At the starting level 6, the same outward-rounded interval pass gives the sharper diagonal enclosure
`a_6 ∈ [-1.6514094855799782e-36, 2.5607381821932904e-36]`, hence
`|a_6| < 3e-36`. The fixed parameter window is strictly contained in `[1.309,1.31]`.
This supplies a quantified initial margin for the diagonal bootstrap; the all-level Lean induction
is a separate formal step.

For each bootstrap step 6–100 it also checks the interval ratio
`R=(c-b)/(c(c+3b))` lies in `(0,0.8)`. The largest upper endpoint is approximately
`0.76386670900639485955066454013148464480…`. The level-6 endpoint values are approximately
`+1.29328974303045258045·10^-140` and `-1.42261871733349783855·10^-36`.

The associated conditional root-shift budget is approximately `9.28792569659442724458·10^-37`.
It assumes the verified finite bootstrap estimates continue to hold at every future level; it is
not an independent all-level certificate. The experiment therefore extends the finite numerical
evidence from transitions through level 14 to a common parameter window checked through level 101,
but it does **not** prove that the bootstrap box is invariant for all levels, nor does it prove
convergence or the limiting quadratic law.

Reproduce it with:

~~~bash
python computational/spectral_gap_theta_2pi/schur_bootstrap_box_iv.py --max-level 101 --dps 180 --radius-digits 140
pytest -q test_spectral_schur_bootstrap_box.py
~~~

The focused regression test takes about nine seconds in the checked environment. The script's
finite-level interval output is computational evidence, not a Lean-kernel theorem or an
infinite-level proof.

The Lean development also records the exact scope of the one-step off-diagonal argument.
Under the coarse pivot/sign box it proves `|b_next| <= (4/5) |b|^2`, then
`b_next in [-6e-37,0]`. A state-coordinate version derives the needed pivot bounds
from the additional explicit assumptions

- `a in [-1e-35,1e-35]`;
- `b in [-6e-37,0]`;
- `lambda in [1.309,1.31]`.

This closes only the one-step preservation of the small signed `b`-coordinate.
The spectral-parameter interval is an assumption of the generic Lean implication, not
yet a Lean theorem about the level-6 root or all subsequent roots. No preservation theorem
for `a` or the derivative/curvature coordinates has been proved, so the full bootstrap
box and the all-level limit argument remain open.



The next coordinate has now been treated by an exact one-step Lean estimate.
The update identity is
`a_next-a = -2*b^2*(c+b)/(c*(c+3*b))`. Under the same coarse pivot box,
the fraction is between zero and one, so

`|a_next-a| <= 2*b^2`.

For the state box used in the level-101 interval experiment, Lean derives the
pivot bounds from `a in [-1e-35,1e-35]`, `b in [-6e-37,0]`, and
`lambda in [1.309,1.31]`, and obtains the explicit increment bound
`|a_next-a| <= 72e-74 = 7.2e-73`.

This is a one-step drift estimate, not yet preservation of the stated
`a`-interval: a proof of that preservation must use the actual interior
margin of the current `a`-bound, or first sharpen the `a`-box. The estimate
does show that the diagonal drift is quadratically controlled by the already
small off-diagonal coordinate. A summability theorem still requires a formal
all-level bound on the successive `b`-coordinates and the root window.



The off-diagonal estimate can now be made linear on the small signed
bootstrap interval. Since
`|b_next| <= (4/5)|b|^2` and `|b| <= 6·10^-37`, the exact
rational comparison `(4/5)(6·10^-37) < 10^-36` yields

`|b_next| <= 10^-36 |b|`.

Lean proves this both from the coarse pivot box and directly from the
state-coordinate box with `a in [-10^-35,10^-35]`,
`b in [-6·10^-37,0]`, and `lambda in [1.309,1.31]`.
The second result derives the midpoint-pivot bounds internally; the lambda
window remains an explicit hypothesis.

This is the geometric-contraction step needed for summing the diagonal
increments. It is still a conditional one-step implication: the state box
and the root window must be established at every level before the geometric
bound can be iterated.



A finite-sum consequence of the geometric contraction is formalized
abstractly in Lean. If u_n >= 0 and u_(n+1) <= (1/2)u_n, then
sum_{k < N} u_k^2 <= 2*u_0^2, and the diagonal estimate
|a_(k+1)-a_k| <= 2*u_k^2 gives |a_N-a_0| <= 4*u_0^2.

The finite-horizon version diagonal_drift_total_le_four_mul_initial_sq_until
requires these hypotheses only for indices before N; its proof extends the
finite segment by zero/constant tails. With u_0 <= 6e-37, Lean further gives
the explicit bound |a_N-a_0| <= 1.44e-72. This is the summable-drift
estimate needed to close the diagonal coordinate once the local Schur
bounds and initial margin are established. The all-level state-box and
root-window induction remain separate obligations, so this is not yet an
unconditional spectral-limit theorem.

The next Lean result, `schurBoundaryTrajectory_state_box`, proves a full
conditional all-level invariant for the exact fixed-parameter Schur trajectory.
For `lambda in [1.309,1.31]` and initial state `|a_0| <= 3e-36`,
`b_0 in [-6e-37,0]`, induction gives `|a_n| <= 1e-35` and
`b_n in [-6e-37,0]` for every n. The proof combines the one-step
`1e-36` contraction with the finite summable diagonal-drift bound.
This closes the state-coordinate invariance conditional on the parameter
window and starting-state enclosure; proving that the actual A1 root and
all common-window endpoint signs satisfy those hypotheses remains open.

### A1 derivative-transition interval certificate (levels 5–14)

The derivative sequence splits into an exact Schur update and a root-motion term. With D_m=f'_m(lambda_m),
\[
D_{m+1}-D_m
=
G_m+\bigl(f'_{m+1}(\lambda_{m+1})-f'_{m+1}(\lambda_m)\bigr),
\]
where
\[
G_m=-2b'_m\frac{c_m+5b_m}{c_m+3b_m}
-4b_m\frac{c_mb'_m-b_mc'_m}{(c_m+3b_m)^2}.
\]
The second term is controlled by f''_{m+1} on the full segment from lambda_m to lambda_(m+1).

An outward-rounded interval calculation at 10,000 decimal digits and root-bracket radius 10^-9400 certifies transitions m=5,...,13. For every transition it checks the A1 root brackets and their order, the negative A1 derivative, the negative off-diagonal coefficient, positive midpoint pivots, and
\[
-0.29<f''_{m+1}(x)<-0.07
\quad (x\in[\lambda_m,\lambda_{m+1}]).
\]
It also certifies the finite-level bounds
\[
\frac{|G_m|}{2^m|b_m|}<0.7,\qquad
\frac{|D_{m+1}-D_m|}{2^m|b_m|}<1,\qquad
\frac{|b_{m+1}|}{|b_m|^2}<0.8.
\]
The largest interval upper bounds in this run are approximately 0.6187181, 0.6187729, and 0.7638668, respectively.

Reproduce the high-precision certificate with:
~~~bash
python computational/spectral_gap_theta_2pi/schur_derivative_certificate.py \
  --max-level 14 --start-level 5 --dps 10000 --radius-digits 9400
~~~

These are finite-level interval certificates, not uniform estimates for every m. If the three bounds above are proved uniformly, then |b_6|<10^-36 and |b_(m+1)|<=|b_m|^2 give the conditional tail majorant
\[
\sum_{m=6}^{\infty}2^m|b_m|
\le
\frac{64\cdot10^{-36}}{1-2\cdot10^{-36}}
<6.41\cdot10^{-35}.
\]
Combined with |D_(m+1)-D_m|<=2^m|b_m|, this would prove convergence of D_m and keep its limit strictly negative. The missing step is a proof that these inequalities persist at every level, not only through level 14.

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
3. Prove the quadratic correction law `δ_(m+1) ≈ c·δ_m²` uniformly in the level. An exact Schur recursion ([note](HIGH_PRECISION_2026-11-06.md)) gives the bottom eigenvalue to 145 digits and shows Delta_(m+1) = c Delta_m^2 with c = 0.4939504899 from level 7 on at that precision (a numerical observation, not a proof). The derivative-transition interval certificate controls root-sampled slopes through level 14; the uniform summability estimates and infinite-level limit remain open.
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
pytest -q test_spectral_gap_high_precision.py test_spectral_schur_decimation.py test_spectral_schur_inertia.py test_schur_bottom_eigenvalue.py
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
| `HIGH_PRECISION_2026-11-06.md` | corrected 260-dps A1-root table, quadratic increment ratios, and A1/E splitting; retracts the erroneous PR #12 note |
| `schur_bottom_eigenvalue.py` | compact independent 260-dps Schur-recursion calculation for A1 and E boundary roots |
| `test_schur_bottom_eigenvalue.py` | regression test for the 260-dps standalone roots and equivalence of the two boundary normalizations |
| `schur_decimation.py` | exact rational three-corner Schur recursion and high-precision `A1`/`E` boundary-root continuation |
| `schur_inertia_certificate.py` | outward-rounded Decimal interval checks and finite-level Schur/inertia certificates for the ground state and first E doublet |
| `schur_bootstrap_box_iv.py` | outward-rounded 180-digit common-window A1 Schur bootstrap experiment through level 101 |
| `test_spectral_schur_bootstrap_box.py` | regression test for the finite common-window signs, bootstrap box, and contraction bounds |
| `audit_triangle_gauge.py` | exact combinatorial, gauge, graph, and sparse spectral audits |
| `../../PhiGenesis/SpectralGap/SignedLaplacianMatrix.lean` | Lean: signed Laplacian, Gram identification, and `λ ≥ 1` |


The A1 characteristic has now been linked directly to the invariant state
box. Writing f_n = a_n + 2*b_n, one exact Schur step satisfies
0 <= f_(n+1)-f_n <= 2*|b_n| throughout the fixed parameter window and
state box. This is the endpoint-sign transport estimate: the lower-end
positive sign is preserved immediately, while the upper-end negative sign
will be preserved after summing the increments using the strong geometric
contraction of b. This one-step result alone does not yet prove the
all-level common root bracket.


The A1 endpoint-sign transport is now formalized for every finite Schur
level under the existing level-six start box. The lower endpoint remains
nonnegative because each A1 characteristic increment is nonnegative.
For the upper endpoint, the strong off-diagonal contraction implies the
coarser quarter-contraction; the finite sum of |b_n| is at most
(4/3)|b_0|. With |b_0| <= 6e-37, the total A1 increase is at most
1.6e-36. Therefore an initial upper-end margin of 1.7e-36 remains strictly
negative at every finite level. This conditional sign-transport theorem
does not itself certify the rational level-six endpoint states or establish
root existence by continuity.


The narrow common parameter window now has exact rational endpoints
encoded in Lean, not rounded floating-point literals:
L = 1.309128920280813421888623088170810187 and
U = 1.309128920280813421888623088170810189.
Unfolding the exact Schur recurrence for six steps from (a,b)=(2-lambda,1),
Lean certifies at both endpoints
|a_6| <= 3e-36 and -6e-37 <= b_6 <= 0.
It also certifies f_6(L)>0 and f_6(U)<=-1.7e-36.
These endpoint certificates discharge the numeric start assumptions
required by the finite-level sign-transport lemmas. They do not yet give
a uniform starting box for every lambda in [L,U] or a continuity/root
existence theorem for later levels.


The exact lower/upper level-six certificates are now combined with the
all-finite-level Schur sign-transport theorems in one Lean result,
`schurBootstrapEndpoints_A1_signs_all_finite_levels`. It states that
the lower rational endpoint has nonnegative A1 characteristic at every
finite Schur level, while the upper rational endpoint has strictly
negative A1 characteristic at every finite Schur level. This is the
common endpoint-sign statement needed for an intermediate-value argument.
It is still only a statement at the two fixed endpoints: continuity of
the level-n characteristic throughout the interval, and a uniform
all-parameter state/pivot enclosure, remain to be proved before inferring
a root at every level.


The finite-level A1 characteristic is now proved continuous at a parameter
whenever every Schur denominator encountered before that finite level is
nonzero there. The Lean result is conditional on this pointwise pivot
nonvanishing; a uniform denominator bound over the full narrow interval
is still required before applying the intermediate value theorem.


A conditional IVT theorem is now formalized: if the two Schur denominators
are nonzero for all parameters in the narrow interval through a fixed
finite level, then the all-level opposite endpoint signs force an A1 root
at that level. The remaining task before unconditional finite-level root
existence is to prove these denominators uniformly nonzero on the interval.


A uniform level-three Schur enclosure has now been formalized over the
full narrow parameter interval: `|a_3| <= 1/500` and
`b_3 in [-1/20000, 0]`. The proof gives positive level-two pivot
denominators. This is the proposed coarse starting box for an all-level
denominator invariant; unconditional root existence and convergence
are not claimed yet.

### Lean: the limit of the selected A1 roots is a root of the limiting A1 characteristic

`schurBootstrapA1AtLevel_rootLimit_is_root` (`PhiGenesis/SpectralGap/SchurBoundary.lean`)
proves, with no hypotheses and with only the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), that the supremum of the increasing sequence of selected finite-level A1 roots of
the scalar Schur recursion is a zero of the continuous limiting A1 characteristic, in the bootstrap
parameter interval `[schurBootstrapLambdaLower, schurBootstrapLambdaUpper]`.

This is a statement about these scalar objects. It does not by itself prove that the selected
roots are the bottom eigenvalues `λ_min(m)` of the graph operators, that `λ_min(m)` converges,
that the root is unique in the interval, or the quadratic law. Those remain open; the next
step is the identification of the A1 branch with the global bottom of the spectrum at every level.

### Scope of the Lean Schur development (as of 2026-11-07)

Formalized in `PhiGenesis/SpectralGap/SchurBoundary.lean`: the scalar Schur recursion
(`schurBoundaryTrajectory`, the `schurBootstrapA1AtLevel_*` family), its uniform tail bound, uniform
convergence on the bootstrap interval, continuity of the limiting A1 characteristic, and
`schurBootstrapA1AtLevel_rootLimit_is_root`.

Not formalized in Lean: (1) a bridge from the graph matrix to this recursion (the level-`m` signed matrix
`sgSignedLaplacianMatrix m` is defined in `SignedLaplacianMatrix.lean`, but there is no
Schur-complement statement connecting it to `schurBoundaryTrajectory`, and the gauge equivalence with the signless Laplacian is formalized only for
quadratic forms (`sgSignedGraphEnergy_eq_gauged`), not used by the Schur development); (2) identification of the selected A1 roots with the bottom eigenvalue
`λ_min(m)` at every level; (3) convergence of `λ_min(m)`; (4) the quadratic increment law. Items (1)–(4)
are open; (1) and (2) are the next steps, in that order.

### Update 2026-11-07: the level-six starting enclosure is a Lean theorem

`schurBootstrapLower_levelSix_certificate` and `schurBootstrapUpper_levelSix_certificate`
(`PhiGenesis/SpectralGap/SchurBoundary.lean`) compute six exact Schur steps from the original state
`(2-λ, 1)` at the rational endpoints `schurBootstrapLambdaLower/Upper` (36 decimal digits) and give
the enclosure `|a_0| <= 3e-36`, `b_0 in [-6e-37, 0]` together with the A1 signs. Earlier remarks in
this file that no Lean theorem about the level-six root exists are superseded by this entry.
