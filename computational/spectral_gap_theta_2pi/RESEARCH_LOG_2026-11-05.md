# Research log: uniform gap for the local-face signing (theta = 2 pi label conditional)

**Date:** 5 November 2026  
**Status:** the analytic lower bound is proved for the explicit local-face operator H = D + A_s defined below. The interpretation of this assignment as the external theta = 2 pi model remains conditional: the cited external sg.py/gap.py sources were not present in the repository or current attachment. This model is not the pivot-zero all-hole-flux representative produced by the repository's default mobius.py solver. The sharper bottom value near 1.30912892028081 remains a numerical observation, not a proved limit.

This is a separate spectral-gap workstream. It is **not** the scalar canonical GF(2) H10 recurrence in computational/higher_moments_z2, and no claim is made that it proves or changes that recurrence.

## 1. Selected direction and rejected shortcut

The supplied 5 November note asks whether the spectral bottom stays away from zero as the gasket level grows. I selected the central theta = 2 pi point, where the connection is represented by central signs and the matrix entries are integral.

I did not adopt the proposed scalar spectral-decimation conclusion. The supplied Schur complement gives different interior and boundary equations; its own test says the interior map matches only 5/38, 30/110, and 125/326 fine eigenvalues in the three tested transitions. That does not establish a global one-variable map for the spectrum. The Schur complement may still be useful, but it needs a boundary-aware eigenvalue classification.

A direct face-wise energy estimate gives a clean result without spectral decimation.

## 2. Recursive graph and signs

Use integer triangular-lattice coordinates v = (i,j), embedded as
\[
(i,j)\mapsto \left(i+\frac j2,\frac{\sqrt3}{2}j\right).
\]
At level 0 the ordered face is ((0,0),(1,0),(0,1)). To pass from level m-1 to m, take three translated copies of the previous ordered faces, in child order 0,1,2, using shifts
\[
(0,0),\quad (2^{m-1},0),\quad (0,2^{m-1}).
\]

For the explicit local-face assignment reconstructed from the convention flux={(f[0],f[1])}, each ordered upward face T=(a,b,c) has signed-adjacency signs s_ab=+1 on the first (horizontal) edge and s_ac=s_bc=-1 on the other two edges. In the repository convention of phi_genesis/mobius.py, signs are sigma=1-2x and the operator is L=D-A_sigma. The local-face model is exactly this operator for x=1 on every first edge (a,b) and x=0 on the other two edges, so sigma=-s and L=D+A_s. This is a specific cochain with odd flux on each elementary upward triangle; it must not be conflated with the separate pivot-zero solution of the hole-boundary-only GF(2) system.

The graph edges are the union of the three edges of each elementary face. In this recursive construction there are 3^m faces; their edge sets are pairwise disjoint; every vertex is covered by at least one face; and
\[
|E_m|=3^{m+1},\qquad |V_m|=\frac{3^{m+1}+3}{2}.
\]
The integer audit is in audit_triangle_gauge.py.

## 3. Exact gauge identity

Define epsilon(i,j)=(-1)^j. The first edge of each ordered face is horizontal, so its endpoints have equal j and epsilon(u)epsilon(v)=+1. On each of the other two edges, j changes by one and the product is -1. Hence, for every edge,
\[
s_{uv}=\varepsilon(u)\varepsilon(v).
\]

Let A_s be the signed adjacency with entries s_uv, A the ordinary adjacency, D the degree matrix, and G=diag(epsilon). With
\[
H_s=D+A_s,\qquad Q=D+A,
\]
we obtain the exact identity
\[
\boxed{H_s=GQG}.
\]
Thus the signed matrix in the supplied mats(m) convention is exactly isospectral to the signless graph Laplacian, not merely numerically close.

In the connection convention H = D - A_U, this same matrix has U_uv = -s_uv. The vertex gauge epsilon sends every link to U'_uv = -1, so the connection holonomy around each elementary triangle is (-1)^3 = -1. Thus the central point is a frustrated pi-flux triangle in a gauge where the matrix is the signless Laplacian.

For the central spin representation U_uv = -s_uv I_2, the operator and gauge are H_s tensor I_2 and G tensor I_2. The spectrum is exactly doubled. This explains the spin doublet at this central point.

## 4. Uniform positive lower bound

For any three vectors x_a,x_b,x_c in a complex Hilbert space, expansion gives the exact identity
\[
\begin{aligned}
&\|x_a+x_b\|^2+\|x_a+x_c\|^2+\|x_b+x_c\|^2\\
&=\|x_a\|^2+\|x_b\|^2+\|x_c\|^2
+\|x_a+x_b+x_c\|^2\\
&\ge \|x_a\|^2+\|x_b\|^2+\|x_c\|^2.
\end{aligned}
\]

Because the elementary faces partition the edges and cover all vertices,
\[
\begin{aligned}
\langle x,Q_mx\rangle
&=\sum_{\{u,v\}\in E_m}\|x_u+x_v\|^2\\
&=\sum_{T\in\mathcal F_m}\sum_{\{u,v\}\subset T}\|x_u+x_v\|^2\\
&\ge\sum_{T\in\mathcal F_m}\sum_{v\in T}\|x_v\|^2\\
&\ge\sum_{v\in V_m}\|x_v\|^2.
\end{aligned}
\]
Therefore, at every level and for scalar- or spinor-valued vectors,
\[
\boxed{Q_m\succeq I,\qquad \lambda_{\min}(H_s)\ge1.}
\]

This proves that the gap cannot close at theta = 2 pi for the stated recursive face/sign model. It does **not** prove convergence of the bottom eigenvalue to 1.30912892028081 or determine its exact limit. The argument needs only edge-disjoint triangular faces and vertex coverage.

## 5. Reproducible checks and numerical evidence

From the repository root run:
    python computational/spectral_gap_theta_2pi/audit_triangle_gauge.py --max-level 10

The script uses exact integer coordinates. It checks recursive face/vertex/edge counts, edge-disjointness, vertex coverage, and the exact edge identity s_uv = epsilon(u)epsilon(v). That edge identity is equivalent to H_s = GQG because the degree matrix commutes with G. It also checks the uniform -1 connection gauge and triangle holonomy.

The audit passes levels 0--10. At level 10 it reports 88,575 vertices, 177,147 edges, and 59,049 elementary faces; each vertex belongs to one or two elementary faces, and degrees range from 2 to 4.

I independently compared the recursive graph with phi_genesis/sg_laplacian.py:sierpinski_graph: vertex and edge sets agree after exact triangular-lattice indexing for levels 0--8.

Exploratory sparse eigenvalue computations gave:
| level | scalar vertices | computed smallest eigenvalue |
|---:|---:|---:|
| 1 | 6 | 1.17157287525381 |
| 2 | 15 | 1.29843788128358 |
| 3 | 42 | 1.30907106525561 |
| 4 | 123 | 1.30912891862700 |
| 5 | 366 | 1.30912892028081 |
| 6 | 1,095 | 1.30912892028081 |
| 7 | 3,282 | 1.30912892028081 |
| 8 | 9,843 | 1.30912892028081 |

These are floating-point eigensolver outputs, not part of the proof. The spin matrix at scalar level 6 has dimension 2,190, matching the scale in the supplied note.

## 6. Evidence boundary

1. The analytic lower bound is proved for the explicit recursive local-face operator specified above.
2. The supplied attachment did not contain the external sg.py/gap.py sources. The face order and sign convention were reconstructed from the pasted code and its six-vertex cell. The graph matches the repository's recursive Sierpinski graph through the audited levels, but exact source-to-source identity with the external faces(m) and operator construction still needs checking.
3. The local-face signing is not the same as the repository's default pivot-zero representative for the all-hole-flux constraints; see the re-audit below.
4. The exact limiting value near 1.30912892028081 remains an observation.
5. The supplied interior and boundary rational maps are not a global spectral-decimation theorem. Any further use must classify boundary data and exceptional modes.
6. No claim is made about general theta, noncentral SU(2) holonomies, Yang--Mills mass gaps, P vs NP, or continuum quantum field theory.
7. This separate workstream does not change the scalar canonical-signing H10 recurrence or its Lean obligations.

## 7. Next steps for the next session

1. Obtain the original sg.py and gap.py; compare ordered faces and edge signs exactly.
2. Formalize the triangle energy identity for Hilbert-valued vectors and the global lower-bound lemma in Lean.
3. Formalize recursive face decomposition, edge-disjointness, and vertex coverage for the exact Sierpinski address model.
4. After the lower-bound theorem is kernel-checked, study the sharper limit. Re-derive Schur elimination with both boundary and interior equations and classify eigenvalue branches before claiming a fixed point.
5. For 0 < theta < 2 pi, compute the local magnetic-triangle coercivity constant and check whether a face-wise estimate survives the chosen connection convention.

**Handoff:** the no-closing-gap question at theta = 2 pi has a clean analytic answer for the explicit model: a uniform lower bound of 1. The exact spectral edge and general-theta case remain open.


## 8. Re-audit of the 4472ddba checkpoint

The initial commit did not trigger a workflow. This is expected from the repository configuration, not evidence of a failed calculation:

- `.github/workflows/lean.yml` watches Lean sources, `lakefile.lean`, `lean-toolchain`, and itself; it does not watch `computational/**`.
- `.github/workflows/tests.yml` runs only on pushes to `main` and pull requests targeting `main`.
- The 4472ddba commit changed only this research log and the Python audit script. Therefore neither existing workflow was eligible to run.

The first audit script also had a weak holonomy assertion: it multiplied a constant expression rather than looking up the three signs stored for each face. The revised script now computes the signed product from the actual edge-sign table.

### Checks rerun in the sandbox

1. Exact face/sign audit, levels 0--10:
   - `|F_m|=3^m`, `|E_m|=3^{m+1}`, and `|V_m|=(3^{m+1}+3)/2`.
   - Every edge belongs to exactly one elementary face.
   - Every vertex belongs to one or two elementary faces.
   - The gauge identity `s_uv = epsilon(u) epsilon(v)` holds on every edge.
   - The repository-sign convention `sigma=-s` has product `-1` around every elementary upward face.

2. Direct graph comparison against `phi_genesis.sg_laplacian.sierpinski_graph`, levels 0--8: vertex and edge sets agree exactly after conversion to integer triangular-lattice coordinates.

3. Lowest eigenvalue of the local-face operator `L=D-A_sigma`, with `sigma=-s`, levels 1--8:
   `1.17157287525381, 1.29843788128358, 1.30907106525561, 1.30912891862700, 1.30912892028081, 1.30912892028081, 1.30912892028081, 1.30912892028082`.
   These are floating-point sparse-eigensolver outputs. They reproduce the earlier table; they are not the proof of the lower bound.

### Crucial comparison with the existing hole-flux solver

The default `phi_genesis.mobius.mobius_spectrum` representative solves one parity-one equation for every listed hole and sets free variables to zero. The local-face assignment instead sets the GF(2) variable to one on each horizontal `(a,b)` face edge and zero on the other two face edges.

For levels 1--6, the local-face assignment has parity zero on every listed hole row, while the default solver requires parity one on every such row. The two representatives differ on 2, 8, 26, 80, 242, and 728 edges, respectively. Their smallest eigenvalues are:

| level | pivot-zero all-hole representative | local-face representative |
|---:|---:|---:|
| 1 | 0.330920911718 | 1.171572875254 |
| 2 | 0.374778207648 | 1.298437881284 |
| 3 | 0.454116460742 | 1.309071065256 |
| 4 | 0.459731121824 | 1.309128918627 |
| 5 | 0.459731877707 | 1.309128920281 |
| 6 | 0.459731877707 | 1.309128920281 |

Consequently, the bound `lambda_min >= 1` is a result for the local-face signing, not for the default all-hole-flux calculation already documented in `mobius.py`. The two matrices have different elementary/hole cycle data and must not be described as gauge-equivalent. The theta = 2 pi label remains conditional until the original external `sg.py` and `gap.py` are inspected.

## 9. Reproducible automation and next steps

A dedicated workflow, `.github/workflows/spectral-gap-theta2pi.yml`, now runs this audit on pushes to `formalize/h10-lean4` that touch the spectral-gap audit, the recursive graph builder, or the hole-flux implementation. It runs four checks: exact face/gauge data through level 10, direct graph comparison through level 8, local-face eigenvalues through level 8, and local-face versus pivot-zero hole-solver comparison through level 6.

Next:
1. Obtain the original external `sg.py` and `gap.py`; verify that their face ordering, edge signs, and matrix convention are exactly this local-face operator before treating the theta label as identified.
2. Formalize the local triangle energy identity and the global lower bound in Lean, together with the recursive face partition/coverage lemmas.
3. Only after source identification and kernel formalization, study whether the repeated numerical bottom is an exact inherited eigenvalue and derive the sharper spectral edge.
4. Keep this local-face workstream separate from the canonical GF(2) H10 recurrence and from the default pivot-zero hole-flux data.

## 10. Lean formalization: local triangle energy

Added PhiGenesis/SpectralGap/TriangleEnergy.lean and imported it from the library root.

The module states and proves:
- trianglePairEnergy_identity: the exact three-pair scalar energy identity;
- trianglePairEnergy_lower_bound: its nonnegative local defect;
- trianglePairEnergy_identity_pi: the same identity summed over an arbitrary finite real coordinate type;
- trianglePairEnergy_lower_bound_pi: the finite-coordinate lower bound.

This is the first kernel-checking block, not yet the global graph spectral theorem. The finite-coordinate version is designed to cover real vector coordinates; a complex or spinor vector can be represented by its real coordinates. The global step still needs a precise finite-face incidence structure, edge partition, and vertex-cover argument.

At this commit the Lean file has been submitted to the repository CI but its kernel build is pending. Do not mark this block formally complete until the Lean workflow succeeds on the exact commit SHA.

The audit report now prints the level number in its first column (previously it mistakenly printed the vertex count under the level heading; the underlying calculations were unchanged).

## 11. Global face-energy block submitted for Lean verification

Added `PhiGenesis/SpectralGap/GlobalFaceEnergy.lean` and imported it into the library root.

The new module makes the combinatorial hypotheses explicit:
- `hEdges`: the map from a face-edge slot to its ordered endpoint pair is injective, so an edge is counted once;
- `cover : V ↪ F × TriangleCorner` with `hCover`: every graph vertex has a chosen incident face-corner, and the chosen slots are distinct.

Under these hypotheses, `faceGraphEnergy_lower_bound` proves

`sum_v x(v)^2 ≤ sum_{edge {u,v}} (x(u)+x(v))^2`.

The proof chain is now local triangle coercivity → sum over faces → no duplicated edge slots → cover every vertex exactly at least once. This is the abstract global theorem needed before instantiating the recursive Sierpinski faces. It is not yet the Sierpinski-instance theorem: the next block must construct the edge-injective map and the corner selector from the actual recursive face list.

Current status: Lean CI on the exact commit is pending. If a compiler error appears, inspect that error and correct the specific proof; do not weaken `hEdges` or `hCover` to bypass it.

Next three blocks:
1. prove the recursive SG face family is edge-disjoint and every vertex has a selected incident face corner;
2. instantiate `faceGraphEnergy_lower_bound` for each level and prove the gauge identity with the repository's sign convention;
3. state the finite-dimensional Rayleigh-quotient/eigenvalue consequence, with the local-face signing clearly distinguished from the pivot-zero all-hole representative.

## 12. Build-tree correction after the first global-energy commit

The first GlobalFaceEnergy commit (9c5844d) was assembled against the older 4472ddba tree instead of its immediate parent tree. This accidentally removed the already kernel-checked TriangleEnergy module and also reverted the spectral-workflow path trigger and the corrected audit output.

The follow-up restoration commit is built on the complete tree of the green 6c8e509 parent and adds the GlobalFaceEnergy module, root import, and this journal entry. It restores the previously checked TriangleEnergy module, the audit workflow's Lean-file trigger, and the corrected audit script. No H10 source is changed.

The failed run #69 therefore reported missing imports caused by an incomplete Git tree; it did not reach typechecking of GlobalFaceEnergy itself. The global module remains unverified until a new Lean build succeeds on the restoration commit.
## 13. Lean failure diagnosis and focused correction

Run #41970854989 reached the new GlobalFaceEnergy module after successfully compiling TriangleEnergy. The failures were:
- derived Fintype instances for the two small enumerated slot types produced malformed enum-list membership obligations under Lean 4.33.1;
- the sum-over-product rewrites did not reduce the three constructors of those slot types;
- two trailing `simp` calls were left after preceding rewrites had already closed their goals.

The repair replaces the derived Fintype instances with explicit three-element `elems`/`complete` instances, keeps the same three slots and mathematical hypotheses, and removes only the two redundant tactic commands. This is a proof-engineering correction, not a weakening of the global inequality.

Status: the focused correction is committed for a fresh Lean build. The global module is not counted as formally verified until that exact build succeeds.
## 14. Second focused correction to global face-energy sums

The restored Lean build now reaches and compiles TriangleEnergy. Run #41971429410 then isolated the remaining failures to the two identities which expand sums over the custom three-constructor corner and edge types.

The previous `simp` attempt rewrote the product sum but did not reduce the custom finite sum. The correction now proves `sum_triangleCorner` and `sum_triangleEdge` explicitly by changing `Fintype.univ` to the exact three-element `elems` finset, then uses those lemmas after `Fintype.sum_prod_type`.

No graph assumptions, injectivity hypotheses, or coverage assumptions were changed. The global inequality proof after these identities is unchanged.

Current commit is pending a fresh `lake build PhiGenesis`; only a successful run on its exact SHA will close this block.
## 15. Parser correction in explicit triangle-slot sums

Run #41971915645 reached `GlobalFaceEnergy.lean` and reported `unexpected token 'in'; expected ','` at the two explicit finite sums. The finite-type instances and sum-over-product expansions were no longer the issue.

The previous correction wrote `∑ corner in S, ...` and `∑ edge in S, ...`, but Lean's Finset binder syntax is `∑ corner ∈ S, ...` and `∑ edge ∈ S, ...`. The next commit changes only these two binder tokens. The intended three-element finite sums and the global theorem hypotheses remain unchanged.

Status: parser fix committed; await Lean CI on the exact SHA before proceeding.
## 16. Surjective corner selection and level-zero instantiation

Added `PhiGenesis/SpectralGap/FiniteFaceCover.lean` and imported it from `PhiGenesis.lean`.

The new `cornerEmbedding_of_surjective` theorem constructs an injective right-inverse selector from mere surjectivity of the face-corner map. This removes the manual embedding obligation from concrete finite face models.

`faceGraphEnergy_lower_bound_of_surjective_corners` packages the global energy inequality using edge-slot injectivity plus surjective corner coverage.

The module then defines the level-zero gasket as one face on `Fin 3`, proves its three corner slots cover all three vertices, proves its three ordered edge slots are distinct, and instantiates the global lower bound as `baseFace_graph_energy_lower_bound`.

Progress assessment: this is the first concrete graph instance of the energy theorem, but only at level zero. The full arbitrary-level Sierpinski theorem is not yet present. The next task is to define the recursive face-address family at level m and prove its edge-slot injectivity and corner-map surjectivity; only then can the global theorem be instantiated for every m.

Lean CI for this block is pending on the exact commit SHA. No H10 source was changed.
## 17. Recursive Sierpinski faces: all-level address model

Added `PhiGenesis/SpectralGap/RecursiveSierpinskiFaces.lean` and imported it from the root.

The face type is the finite function type `Fin m → Fin 3`. Its origin is defined recursively: the leading digit selects one of the three child copies, translated by `(0,0)`, `(2^m,0)`, or `(0,2^m)`, and the tail determines the position inside that child.

The module proves the child boxes are disjoint, the address-to-origin map is injective, every coordinate vertex in the finite image is represented by a face-corner slot, and the ordered edge-slot map is injective. The resulting theorem `sg_graph_energy_lower_bound` instantiates the global face-energy inequality at every natural level.

This closes the combinatorial hypotheses of the abstract energy theorem for the recursively defined address graph, if the exact Lean build passes. The remaining model-identification task is to connect this address graph to the repository's coordinate/index-based `sierpinski_graph` implementation and the signed operator convention. The proof here is for the abstract recursively defined face graph, not yet for the default pivot-zero hole-flux matrix.

Current exact commit SHA is awaiting Lean and Python workflows. Do not label the global spectral-gap theorem complete until the Lean kernel build succeeds and the graph/sign identification is proved.
## 18. First Lean failure and exact proof repair

Lean run #41975849562 reached the new recursive module and identified three local proof-engineering issues:
- the box-separation arithmetic needed the explicit positivity fact `0 < 2^m`;
- the edge-slot case split needed to discharge the mixed-direction cases by arithmetic before reconstructing an address;
- the finite subtype vertex type needed an explicit classical `DecidableEq` instance for the graph-energy definition.

The follow-up changes add only these missing facts and refine the case split. No geometric definition, coordinate, face family, or theorem hypothesis is changed.

Run #41975849503 (Python local-face audit) succeeded on the original recursive-address commit. Lean build on the repair commit is the deciding verification.
## 19. Coordinate-level repair of recursive edge proofs

Run #41976228574 showed the previous repair still left pair equalities opaque to `omega`. In particular, `sgAddOffset_injective_on_box` passed a product equality directly into arithmetic, and `sgFaceEdgeCoords_injective` split endpoint pairs only one level but did not split each point into its two coordinates.

The current repair explicitly applies `congrArg Prod.fst` and `congrArg Prod.snd` to the translated-origin equality. For edge slots it applies `Prod.mk.inj` three times, exposing the four scalar coordinate equalities before any arithmetic reasoning. The remaining cases are then separated into same-direction cases (recover the face origin, then use address injectivity) and mixed-direction cases (contradict the scalar endpoint equations).

This changes no coordinates, offset definitions, or theorem statements. The next Lean run determines whether these coordinate-level proofs now close.
## 20. Gauge-transformed signed energy and all-level lower bound

Added `PhiGenesis/SpectralGap/SignedGaugeEnergy.lean` and imported it into the root.

The row gauge is `epsilon(i,j)=(-1)^j`, defined by parity. The module proves that every local face-edge sign is the product of its endpoint gauges: the horizontal/base edge has sign +1, while the two other face edges have sign -1.

`sgSignedGraphEnergy` defines the corresponding signed quadratic form with each graph edge counted once. `sgSignedGraphEnergy_eq_gauged` proves it equals the ordinary pair energy after applying the diagonal vertex gauge. Combining this identity with `sg_graph_energy_lower_bound` gives `sgSignedGraphEnergy_lower_bound` for every level m.

Under the repository sign convention `sigma=1-2*x` and `L=D-A_sigma`, the local-face assignment has `sigma=-s`, so this energy is the quadratic form of `D+A_s = D-A_sigma`. The theorem is therefore an all-level quadratic-form lower bound `xᵀLx ≥ ||x||²` for the explicit local-face signing.

Scope: this is not the pivot-zero all-hole-flux representative in `mobius.py`; those cycle constraints differ. It is also not yet a matrix-eigenvalue theorem: the next formalization should define the signed Laplacian matrix from the finite edge set and derive the Rayleigh/eigenvalue statement from this quadratic-form bound.

Lean and Python CI are pending on the exact commit SHA.
## 21. Explicit same-row gauge product helper

Before relying on CI, source review caught that the face-sign proof referenced `sgRowGauge_mul_self` without yet defining it. Added the missing helper directly from `sgRowGauge_sq` using `pow_two`. This is a small proof dependency omission caught before treating the gauge block as complete; no mathematical statement or sign convention changes.

Lean/Python workflow results for this revision are pending.
## 22. Explicit normalization in the gauge-term identity

During source review, the first `hinner` subproof was found to rely on `rw [hgu]` closing the residual `1 * x` expression by definitional reduction. Added `ring` after the rewrite so the algebraic normalization is explicit. The identity itself and all hypotheses are unchanged.

CI is being rerun on this exact source revision; the preceding Mathlib cache attempt failed before Lean compilation due to 28 transient broken-pipe downloads, not due to this module.
## 23. Mark graph energy noncomputable for the classical finite-vertex equality

Lean run #41978775853 attempt 2 typechecked the earlier spectral-gap modules, including RecursiveSierpinskiFaces, and then reported that `sgSignedGraphEnergy` depends on the noncomputable `sgVertexDecidableEq` instance. The energy definition therefore needs the `noncomputable` modifier; the mathematical quantity is still a finite sum over the same edge finset.

The same run also exposed the residual `1 * x` goal in the earlier 22a587 source. The current parent 3ff2e1f already adds `ring` immediately after `rw [hgu]`, which explicitly closes that algebraic normalization. This commit only marks the edge-energy definition noncomputable.

Lean and Python checks are pending on the new exact SHA.

## 24. Green verification of the signed-gauge energy block

On commit `37a83b768d070e6e6b1a83dc36f1fe76d79df722`, Lean workflow run [#41979152426](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41979152426) completed successfully. The `Build formalization` step ran `lake build PhiGenesis` and passed. The exact local-face Python audit [#41979152625](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41979152625) also completed successfully. Thus `SignedGaugeEnergy.lean` is typechecked on this exact SHA; this is not merely a cache/setup success.

## 25. Explicit matrix realization and eigenvalue consequence

The next formal block defines the finite signed Laplacian matrix as a sum of rank-one edge matrices built from the signed endpoint vector. It proves entrywise symmetry and identifies its quadratic form exactly with `sgSignedGraphEnergy`. The already verified all-level quadratic-form estimate then implies that every real eigenvalue admitting a nonzero real eigenvector is at least one.

Scope is kept explicit: the matrix represents the local-face signing `s_uv = epsilon(u) epsilon(v)` established in `SignedGaugeEnergy.lean`. This does not identify that signing with the pivot-zero all-hole-flux representative; the latter remains a separate spectral problem. The new matrix and eigenpair statements await Lean CI on their exact commit.

## 26. Repair of the first matrix formalization compile errors

Lean run [#41980056963](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41980056963) reached `SignedLaplacianMatrix.lean` and reported three source-level issues: (i) the endpoint-indicator sum was not reduced by the initial `simp`; (ii) two intermediate `calc` steps in the finite rank-one quadratic-form rearrangement omitted the surrounding scalar factor; and (iii) `λ` was used as a binder name although it is reserved Lean syntax.

The repair gives the indicator sum an explicit finite-sum proof, keeps the external scalar factor in both sum-reordering steps, and renames the eigenvalue variable to `eigval`. No graph definition, sign convention, energy identity, or theorem hypothesis is changed. Python audit [#41980056972](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41980056972) passed on the parent source. This repair is not closed until a fresh Lean build on its exact SHA succeeds.

## 27. Second source-level repair in the matrix block

The rerun [#41980725248](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41980725248) compiled the preceding spectral modules and reported three remaining proof issues in `SignedLaplacianMatrix.lean`: the edge-vector sum needed explicit distribution before applying the indicator-sum helper; the scalar factor in the inner vertex sum had to be reassociated before `Finset.mul_sum`; and strict positivity of a nonzero coordinate square needed an explicit `sq_pos_of_ne_zero` proof. The repair makes each of these steps explicit. No mathematical definition or theorem assumption is altered. The Python audit passed on the parent SHA; Lean must pass on this new exact commit before this block is closed.

## 28. Gram factorization of the local signed Laplacian

The verified matrix module is now extended with an explicit signed edge-incidence matrix `B), indexed by the recursive face-edge slots. Each row has coefficient (1) at the first endpoint and the endpoint-gauge product (s_{uv}) at the second. Using the proved injectivity of the face-edge endpoint map, Lean identifies the existing finite-graph matrix exactly as `B.transpose * B`. Thus the local-face matrix is the standard signed Laplacian (D-A_\sigma) in the repository convention `\sigma=-s), not merely a matrix with the same energy formula.

A second theorem states the full Rayleigh inequality directly at matrix level:
`sum_v x_v^2 ≤ sum_u x_u (Lx)_u`.
The earlier eigenvector corollary remains as a consequence.

The distinction from the pivot-zero all-hole-flux model remains essential. The exact audit reports local-face hole parity zero and pivot-zero target parity one; the two signings are not switching-equivalent. The new Gram and Rayleigh theorems are only for the local-face model. The next mathematical task is to formalize the actual hole-boundary GF(2) constraints and the pivot-zero representative, reusing the general incidence/forest machinery only after the exact edge-order identification is established. This extension awaits Lean CI on its exact SHA.

## 29. Remove a tactic after the Gram-factorization goal was already closed

Lean run [#41984179386](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41984179386) typechecked the new Gram-factorization proof through the final rewrite. The only reported error was `No goals to be solved` at the following standalone `simp`: `rw [Finset.sum_image hinj]` had already discharged the equality. The correction removes that redundant tactic line only. The factorization statement and injectivity argument are unchanged. A new exact-SHA Lean build is required before marking the extension complete. Python audit [#41984179303](https://github.com/RFT-SIRM/Phi-Genesis/actions/runs/41984179303) passed on the parent.


## 30. Reproducible high-precision spectral regression test

The high-precision calculation was independently rerun in a clean Python runtime with NumPy 2.3.5, SciPy 1.17.0, and mpmath 1.3.0. Levels 2–5 reproduced the README bottom eigenvalues to the displayed digits. At level 5, the three-vector Rayleigh–Ritz calculation returned a block residual of approximately 8.69e-21; the individual eigenpair residuals were all below 4e-21. The bottom-to-second-mode splitting was approximately 2.0265e-18. These are numerical residual diagnostics, not interval bounds.

Added test_spectral_gap_high_precision.py to make the computation part of the ordinary fast test suite. It checks the four tabulated bottom eigenvalues, the low-cluster residuals, and the level-5 splitting. The test explicitly labels the tolerances as reproducibility checks, not formal certification. The README reproduction commands now include this test.

The new test commit is dd1753782696c094790d70868da3709693948183. The original PR #11 CI was green before this test was added; the new exact SHA requires its own CI run before the test integration can be considered verified.


## 31. Level-six refinement and complete S3-sector audit

The level-six bottom eigenvalue was recomputed independently in the fully symmetric `A1` quotient (dimension 186) using 70-digit arithmetic and dense multiprecision inverse iteration. The result is `1.309128920280813421888623088170810187650767803108018768…`, with residual `6.02e-47`. The corresponding level-5 value is `1.309128920280813420537624946411459383001454565271922517…`, with residual `7.65e-47`.

The standard `E` sector was computed independently using its sparse complex Hermitian quotient and multiprecision Jacobi-PCG inverse iteration. At level 5 its lowest eigenvalue is `1.309128920280813422564122159050485604428893059246181191…` (residual `1.24e-41`). At level 6 it is `1.309128920280813421888623088170810189003102475121980131…` (residual `1.30e-41`). The `A1`–`E` splitting therefore falls from `2.0264972126390262214e-18` at level 5 to `1.3523346720139613627e-36` at level 6. This is an extremely close near-degeneracy, not exact equality at the precision computed.

The alternating `A2` quotient has dimensions 5, 18, 58, and 179 at levels 3–6. Its lowest eigenvalue is 2 at all four levels; the level-6 inverse-iteration residual is `6.81e-28`. The full representation dimensions at levels 2–5 decompose as `dim(A1)+dim(A2)+2 dim(E) = |V|`; the sorted union of independently built sector spectra matches the full dense graph spectrum with maximum float64 discrepancy between `3.6e-15` and `1.51e-14`. At level 6 the dimensions are `186 + 179 + 2·365 = 1095`.

The fully symmetric `A1` bottom is therefore the global bottom in these calculations; the `E` sector provides the next pair at a separation of about `1.35e-36` at level 6. The level increments and ratios are `δ_5=1.65381018320039801986e-9`, `δ_6=1.35099814175935080465e-18`, `δ_5/δ_4²=0.4941153170828634`, and `δ_6/δ_5²=0.4939504986563759`. The conditional one-step extrapolation based on the last ratio is `λ_∞≈1.3091289202808134218886230881708101885523…`; it is not a proof, interval bound, or exact value.

These computations are independent numerical checks performed in a clean local runtime. The repository CI on the earlier `b133fc2` SHA passed the ordinary non-nightly test suite. The follow-up correction that makes the script compute all consecutive ratios dynamically is committed separately and requires its own exact-SHA CI run. No full level-six interval certificate is claimed.

## 32. Levels seven and eight; sparse-LU/multiprecision refinement

A separate high-precision local calculation extended the fully symmetric sector to level 8 and the complex standard-representation sector to level 7. The level-7 `A1` value is
`1.309128920280813421888623088170810188552324251117326343433535984452681697002915034786490069389197961…`,
with residual `2.18e-94`. The level-7 `E` value is
`1.30912892028081342188862308817081018855232425111732634343353598445268169760514245722344731949215782007648…`,
with residual `1.82e-77`. The observed difference is about `6.02227422437e-73`; both residuals are smaller than that difference. This remains a multiprecision numerical result, not an interval certificate.

The level-7 dimensions are `dim(A1)=551`, `dim(A2)=543`, and `dim(E)=1094`, with `551+543+2·1094=3282`. The low modes in `A1` and `E` are followed by eigenvalues near 2; the numerical gap to the next mode is about `0.69087108`. The alternating `A2` sector's lowest eigenvalue remains 2 in the level-7 sparse float64 spectral check. A full level-7 spectrum reconstruction has not been done.

The level-8 `A1` value is
`1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341948933027533567445524…`,
with residual `1.04e-97` and dimension 1645. The independent level-8 `E`-sector calculation and its splitting from `A1` are recorded in section 33 below.

The positive increments and latest ratios are:
- `δ_7 = 9.01556448009307575100636291381781697002915e-37`
- `δ_8 = 4.01484948291304833401973239259953413011432912771828840881734659026453419489330275335674455e-73`
- `δ_9 = 7.96199603289170721200e-146…`
- `δ_7/δ_6² = 0.4939504899001989666185600009…`
- `δ_8/δ_7² = 0.4939504899001989528562882789…`
- `δ_9/δ_8² = 0.4939504899001989528801830492…`

The latest two ratios agree to about 19 significant digits. This is empirical evidence for the quadratic correction pattern, not a proof of convergence or of the law for all levels.

To improve runtime without discarding high-precision residual checks, the script now includes a sparse-LU preconditioner formed in float64 and iterative refinement whose residuals, matrix-vector products, normalization, and Rayleigh quotient are evaluated in `mpmath`. The solve tolerance scales with the working precision. Regression tests compare the new solver against the previously established level-6 `A1` and `E` values. The CLI supports optional `--mixed-precision-levels`, `--mixed-precision-sectors`, `--mixed-precision-dps`, and `--mixed-precision-iterations` arguments.

The level-7 through level-9 calculations above were obtained in independent local numerical runs. The repository implementation is covered by the level-six regression tests; exact-HEAD CI on code commit `592c7b2a1bd51c076718126def9df3837c882f7b` passed with 74 tests passed and 8 nightly-marked tests deselected. The high-level numerical runs themselves are not CI tests.

## 33. Level-eight E-sector splitting and level-nine A1 increment

The sparse-LU/multiprecision solver was independently exercised beyond its level-six regression tests. The implementation change uses SuperLU's sparse float64 L/U factors but performs forward and backward substitutions, residual evaluation, and correction accumulation in `mpmath`. This avoids the previous `float64` correction-rounding floor near `1e-16`.

At level 8, the fully symmetric sector has dimension 1,645 and the complex `E` sector has dimension 3,281. Their computed bottoms at 170 decimal digits are:

- `A1_8 = 1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341948933027533567445524…`
- `E_8 = 1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341960876021582905006341…`

The final residuals are `1.04169265081e-97` in `A1` and `9.45013277976e-98` in `E`; the maximum relative linear-solve residuals are `4.10410290987e-109` and `1.77880357893e-111`, respectively. The observed sector splitting is

`E_8-A1_8 = 1.1942994049337560817e-145…`.

The float64 low-spectrum check places the next sector eigenvalues near 2, approximately `0.69087108` above the bottom. With this numerically observed separation, residual-squared Rayleigh error estimates are about `1.6e-194` and `1.3e-194`; they are far below the splitting, but they are not interval certificates.

The ratio of the sector splitting to the square of the corresponding level increment is:
- level 7: `(E_7-A1_7)/δ_7² ≈ 0.74092573485035102486…`
- level 8: `(E_8-A1_8)/δ_8² ≈ 0.74092573485029842926…`

These agree to about 13 significant digits. This is a second empirical scaling coefficient, distinct from the increment recurrence coefficient.

The level-nine fully symmetric quotient has dimension 4,926 in a graph with 29,526 vertices. Its 170-digit calculation gives

`A1_9 = 1.30912892028081342188862308817081018855232425111732634343353598445268169740439998307779490279117120025995341301143291277182884088173465902645341956895023566459152736…`

with residual `8.10883078756e-98` and maximum relative linear-solve residual `4.10410290987e-109`. The actual increment and quadratic ratio are:

- `δ_9 = A1_9-A1_8 = 7.96199603289170721200e-146…`
- `δ_9/δ_8² = 0.4939504899001989528801830492…`

This agrees with the level-eight ratio `0.4939504899001989528562882792…` to about 19 significant digits. The one-step conditional prediction from level 8 was `7.96199603289170721161e-146`; the measured level-nine increment differs from that prediction only at relative scale about `5e-20`.

Using the latest ratio, the next conditional increment is approximately `δ_10 ≈ 3.13131915163e-291`. This is an extrapolation only. The `A2` and `E` sectors at level 9 have not been computed, so no full level-nine spectral decomposition or global-bottom claim is made.

The exact-HEAD GitHub CI for code commit `592c7b2a1bd51c076718126def9df3837c882f7b` passed: 74 tests passed and 8 nightly-marked tests were deselected. That CI covers the new mixed-precision solver's level-six `A1` and `E` regression tests; the level-eight and level-nine numerical runs above were independent local calculations and are not CI tests.

The dense `A1` quotient assembly has now been replaced in the mixed-precision path by sparse orbit-neighbor rows. The new builder is regression-compared against the dense reference at levels 2–5, and the existing level-six mixed-precision `A1` test exercises it. Its exact-HEAD CI result is pending. Next numerical bottlenecks: attempt the level-ten `A1` bottom with this sparse builder and compute the level-nine `E` sector if the splitting law is to be tested one level further. The convergence theorem, exact limit, interval certification, and identification with the external theta=2π operator remain open.

## 34. Level-nine/ten precision campaign and run audit (2026-11-06)

The dedicated high-precision workflow was audited after a long-running GitHub Actions execution. On run `42165804193` (code/workflow SHA `43a5496c9e25d2a57438635343ce0ed8680a62bc`), the `A1` level-10 step completed successfully, while the `E` level-9 step was still in progress after about one hour. The run used only 110 outer iterations; the `E9` step used 200 decimal digits. A successful process exit alone does not establish that the level-10 increment or the level-9 `A1`–`E` splitting was resolved to the required scale. No numerical value from this run is promoted into the result tables until its complete output and residual are inspected.

The target scale inferred from the previously observed recurrence is `δ_10 ≈ 3.13e-291`; the expected `E9-A1_9` splitting is also on the order of `1e-291`. For this reason the new campaign computes `A1_9`, `A1_10`, and `E9` independently and in parallel, so the two differences use the same working precision and solver settings.

The revised dedicated workflow in `.github/workflows/spectral-gap-high-precision.yml` requests 360 decimal digits, a relative linear-solve target of `1e-210`, 250 outer inverse iterations, and progress output every 20 iterations. Each job stores its own log artifact. The script's `--mixed-precision-only` mode skips the routine level-2-to-6 demonstration calculations, avoiding duplicated baseline work in each job. The new CLI behavior has a regression test covering its precision argument and progress output.

Run `42172159096` was cancelled while it was still in the baseline level-2-to-6 diagnostic portion; its logs contain no level-9 or level-10 high-precision result. Run `42172310562` failed before computation because the workflow passed a literal backslash as a Python argument; the shell continuation was corrected in commit `4f14218df0e5e05d17f7a8d0557236b8fb6a29da`. These are orchestration/configuration failures, not spectral results.

At the time of this entry, the corrected parallel campaign is run `42172447828` on SHA `4f14218df0e5e05d17f7a8d0557236b8fb6a29da`, with three jobs (`A1_9`, `A1_10`, `E9`) executing. The fast test run covering the mixed-only CLI regression is also in progress. No level-9/10 numerical outputs from the corrected campaign are yet asserted here.

Using the latest increment coefficient `c_A=0.4939504899001989528801830492…` and `δ_9=7.96199603289170721200e-146…`, the conditional prediction is `δ_10≈3.1313191516313432757046040823810254e-291`. Using the latest sector-splitting coefficient `c_E=0.74092573485029842926…`, the conditional level-nine splitting prediction is `E_9-A1_9≈4.6969787274470149131748052224579652e-291`. Both are extrapolations used to choose computational precision, not assumed results.

The numerical target is intentionally conservative: if the observed separation to the next mode remains approximately `0.69087108`, a residual below `sqrt(0.69087108·4.70e-291)≈5.70e-146` makes the residual-squared Rayleigh diagnostic smaller than the expected sector splitting. The `1e-210` linear-solve target controls only the accuracy of each linear solve; it does not certify eigenvector convergence. A rough inverse-iteration contraction estimate uses `(λ_1-1)/(λ_2-1)≈0.309/1.0` and a float64-seeded starting vector, placing 250 outer iterations near `1e-143` residual scale, which may be several orders above the `5.70e-146` acceptance target. The final measured Ritz residual is therefore decisive; if it exceeds the target, increase the iteration count and rerun. This remains a numerical diagnostic, not an interval certificate.

The main convergence theorem, exact limit, full spectral proof at levels 9–10, interval certification, and identification with the external theta=2π operator remain open.

## 35. Exact A1 boundary Schur recursion and level-12 roots (2026-11-06)

A separate exact finite-level reduction has been derived for the fully symmetric A1 sector. Let S_m(λ) be the 3×3 Schur complement of Q_m-λI onto the three outer corners after all other vertices are eliminated. S3 symmetry forces S_m=(a_m-b_m)I+b_m J. At level zero, a_0=2-λ and b_0=1.

When three level-m cells are glued, their three midpoint vertices are shared pairwise. The child Schur complements each contain a -λ term at a child corner, so the midpoint diagonal in the global assembled boundary matrix needs a +λ correction: each midpoint is counted in two child boundary matrices but only once in the global -λI. In the outer-corner/midpoint ordering, the assembled 6×6 matrix is

\[
\begin{pmatrix}
a_m I_3 & b_m T\\
b_m T^T & (2a_m+\lambda-b_m)I_3+b_mJ_3
\end{pmatrix},
\qquad T=J_3-I_3.
\]

Eliminating the midpoints gives the exact rational update, with c_m=2a_m+λ-b_m:

\[
a_{m+1}=a_m-\frac{2b_m^2(c_m+b_m)}{c_m(c_m+3b_m)},\qquad
b_{m+1}=-\frac{b_m^2(c_m-b_m)}{c_m(c_m+3b_m)}.
\]

The A1 boundary-characteristic equation is a_m(λ)+2b_m(λ)=0, provided the eliminated interior block is nonsingular. The recursion is exact algebraically; numerical root continuation does not alone prove that the selected branch remains the lowest A1 eigenvalue at all levels.

Validation:
- Direct dense Schur complements built from the graph matrices at levels 0–4 were compared at λ=1.234, 1.309, and 1.411. The maximum discrepancy was less than 1.4e-16 in float64.
- The forward-mode derivative of the scalar characteristic was compared with mpmath.diff at levels 0–6.
- The continued root sequence through level 6 agrees with the independent mixed-precision A1 quotient result. Its continuation through levels 9–12 is an independent exact-recursion calculation, not a direct diagonalization of those full quotient matrices.
- The new regression suite contains direct Schur-complement checks, derivative checks, a level-12 root/ratio check, and a guard against silently repeating a root when requested precision is insufficient. Local isolated run: 24 tests passed.

The 360-dps/420-dps and 700-dps/1250-dps Schur calculations give:
- δ_10 = 3.1313191516313432752501730259366883447320897694671e-291
- δ_11 = 4.8432634024785628097667893707639166280078554951701e-582
- δ_12 = 1.1586695622247229657100023109242926292894362355858e-1163

The ratios δ_10/δ_9², δ_11/δ_10², and δ_12/δ_11² agree near
0.493950489900198952856288279653540948210748109987…

The recursion also exposes a conditional asymptotic mechanism. At a level-m root, a_m=-2b_m, so
f_(m+1)(λ_m)=-2b_m(c_m+5b_m)/(c_m+3b_m). If λ_m→λ∞ and b_m→0, the exact update implies
b_(m+1)(λ_m)/b_m(λ_m)²→-1/λ∞. If in addition f'_(m+1)(λ_m)→L≠0, then Taylor expansion yields
δ_(m+1)/δ_m²→(1/λ∞)/(-2/L). The observed derivative factor is
-2/L≈1.54644387367797039232151350963469…; the other factor is
1/λ∞≈0.76386670900639485955066454013148…. Their quotient reproduces the observed quadratic coefficient. Neither convergence nor the derivative limit has yet been proved, so this is a proof strategy, not a theorem.

CI correction status: the earlier ordinary test run failed only because a substring assertion confused the valid line mixed A1 level 2: n=... with the baseline-only line A1 level 2: n=.... Commit d91bb227c5d4acbf7cb8b2db5ff5f40c0243cca7 anchors that assertion to the start of each output line. Exact-SHA test run 42173641928 passed: 79 passed, 8 deselected.

The separate high-precision workflow run 42172777291 remains in progress on code SHA 4565d362b80fc7c36e03351014e0abfaee2c6193, with independent jobs for A1_9, A1_10, and E_9. Its configured 250 outer inverse iterations must not be assumed sufficient: final Ritz residuals need to be checked against 5.70e-146 before using either expected 1e-291 difference. The exact A1 recursion is a new independent check of the A1 boundary-root sequence; it does not replace the E_9 computation or its independent residual inspection.

The convergence theorem, interval certification, proof that the continued root is the bottom of A1 at every level, and identification with the external theta=2π operator remain open.


## 36. E boundary channel from the same Schur recursion (2026-11-06)

The boundary Schur matrix is S_m=(a_m-b_m)I+b_mJ. The constant corner vector is the A1 channel, with scalar characteristic f_m=a_m+2b_m. On the two-dimensional corner subspace orthogonal to (1,1,1), J vanishes, so the standard E-boundary characteristic is g_m=a_m-b_m. No separate matrix assembly is required. The same rational recursion therefore continues both boundary roots.

The E root sequence is initialized at levels 1 and 2 and then continued downward by high-precision Newton steps. Its levels 5–8 agree with the previously computed bottom eigenvalues of the full E quotient to the displayed precision. The level-9–11 values below are independent Schur-boundary roots and still await the independent full E-sector matrix calculation in workflow 42172777291.

The computed E-boundary minus A1-boundary splittings are:
- level 9: 4.6969787274470149128752595389050325170981346542007e-291
- level 10: 7.2648951037178442146501840561458749420117832427551e-582
- level 11: 1.7380043433370844485650034663864389439341543533787e-1163

Dividing these by the squared A1 increments gives the stable coefficient
0.74092573485029842928443241948031142231612216498… . This is 3/2 times the A1 coefficient 0.493950489900198952856288279653540948210748109987… at the available precision.

An even sharper relation appears numerically:
(E_m-A1_m)/(A1_(m+1)-A1_m) → 3/2.
An independent 2,450-dps recomputation resolves the deviations from 3/2 as approximately:
- m=7: 1.212619483e-71
- m=8: 4.770512016e-144
- m=9: 3.736959211e-289
- m=10: 1.153626845e-579
- m=11: 5.514032e-1161.
Thus the corresponding agreement is about 70, 143, 288, 578, and 1,160 decimal places. This corrects the earlier level-index shift in the first report. These are high-precision numerical comparisons, not interval-certified bounds.

The E-boundary continuation is now explicitly regression-compared with the independent full E-sector matrix values at levels 5–8. An additional 2,450-dps test checks the 3/2 relation through level 11; the test only asserts the displayed numerical precision and does not promote it to a theorem.

Conditional derivation: at an A1 root f_m=0, hence a_m=-2b_m and g_m=a_m-b_m=-3b_m. The next A1 characteristic at the same point is
f_(m+1)(λ_m)=-2b_m(c_m+5b_m)/(c_m+3b_m)≈-2b_m.
If g'_m(λ_m) and f'_(m+1)(λ_m) approach the same nonzero limit L, the two root shifts are approximately 3b_m/L and 2b_m/L, producing the 3/2 relation. This in turn yields the conditional relation c_E=(3/2)c_A1. The derivative-limit and root-convergence hypotheses still need proof.

The extended A1/E Schur test module now has 30 test cases: direct Schur-complement comparisons, forward-derivative checks, A1 level-12 roots, E/A1 splitting, independent E-matrix comparisons at levels 5–8, the 3/2 shift-ratio check at 2,450 dps, and insufficient-precision guards. The preceding A1-only implementation commit 8208de4 passed its exact-SHA GitHub CI: 103 passed, 8 deselected. The current E-extension commit will receive its own CI run.

The E-sector full matrix job in workflow 42172777291 was still in progress at the last check. Do not treat the Schur E9–E11 roots as already cross-checked by that separate matrix job. The alternating A2 sector at level 9 and the global bottom-mode certification remain open.


The ordinary CI for the preceding E-extension SHA f29353313bb1c30cb3f30db6badd04ff839b1061 passed on exact HEAD in run 42175671043: 104 passed, 8 deselected. The follow-up test/log correction adds independent E-matrix anchors and fixes the decimal-order indexing in the 3/2 comparison; it requires its own exact-SHA CI.


## 37. Outward-rounded finite-level Schur/inertia certificate (2026-11-06)

The exact boundary Schur recursion has now been combined with outward-rounded interval arithmetic and Sylvester inertia. This upgrades the finite-level A1/E branch calculations from high-precision numerical roots to a computer-assisted finite-level spectral-order certificate.

For each level m=1,...,12, the A1 boundary-characteristic root was bracketed at 2,450 decimal digits with radius 10^-2390. For each level m=1,...,12, the E boundary-characteristic root was bracketed independently in the same way. The root finder only supplies candidate centers: the interval verifier checks the sign change at the exact decimal endpoints and verifies that the characteristic derivative is strictly negative throughout the full bracket. Thus each bracket contains exactly one root of its boundary characteristic.

At every step k=0,...,m-1 in the cell-gluing recursion, the midpoint elimination block is C_k=c_k I+b_k J. Its eigenvalues are c_k (multiplicity two) and c_k+3b_k (multiplicity one). The interval checker verifies both lower endpoints are strictly positive throughout each root bracket, before performing the next Schur division. Therefore the full principal block on all non-corner vertices is positive definite, by induction over the three-cell assembly.

At an A1 root, a_m+2b_m=0 and b_m<0, so the three boundary Schur eigenvalues are 0 and -3b_m,-3b_m, all nonnegative. Since the eliminated interior block is positive definite, Sylvester inertia proves that Q_m-lambda I is positive semidefinite with a one-dimensional kernel. The A1 root is therefore the simple global smallest eigenvalue.

At an E root, a_m-b_m=0 and b_m<0, so the boundary Schur eigenvalues are 3b_m<0 and 0,0. The positive interior block and Sylvester inertia then show that Q_m-lambda I has exactly one negative eigenvalue and a two-dimensional kernel. The E root is therefore the second eigenvalue, with multiplicity two; every other mode (including A2) lies above it. The A1 and E root intervals are strictly disjoint and correctly ordered at every level 1–12.

The checker uses Python Decimal arithmetic with explicit ROUND_FLOOR and ROUND_CEILING for every endpoint operation. It verifies all 24 root brackets and all intermediate midpoint pivots. The smallest lower bound found for any midpoint-pivot eigenvalue is greater than 1.151628330238438… . At level 12 the certified E/A1 root separation is about 9.9470402734076901640e-2327. The finite-level certificate does not rely on the large sparse eigensolver, although the previous direct matrix computations at levels 5–8 remain independent cross-checks.

The reproducible command is:
~~~bash
python computational/spectral_gap_theta_2pi/schur_inertia_certificate.py --max-level 12 --dps 2450 --radius-digits 2390
pytest -q test_spectral_schur_inertia.py
~~~

Local isolated validation of the interval/inertia logic: all 24 (A1,E) level checks passed, with a minimum midpoint-pivot lower bound above 1.1516. The new regression test runs the complete 12-level certificate from scratch. GitHub CI for this exact source revision is required before marking the repository integration closed.

This is a finite-level computer-assisted interval/inertia result, not a Lean-kernel theorem. It does not prove convergence as m tends to infinity, the quadratic correction law for all levels, or identification with the absent external theta=2pi operator. It does, however, close the finite-level global-bottom and first-excited-doublet ordering for the local-face graph at every level 1 through 12.

The sign of the two first-order root shifts is positive: both b_m and the limiting derivatives L are negative, so 3b_m/L and 2b_m/L are positive. The previous draft displayed an erroneous leading minus sign in these two shifts; the ratio 3/2 and all numerical coefficients were unaffected.


## 38. Corrected 260-dps A1/E Schur report and boundary-shift convention (2026-11-06)

The updated standalone report `HIGH_PRECISION_2026-11-06.md` and script `schur_bottom_eigenvalue.py` provide a compact independent evaluation of the same three-corner Schur recursion. The report explicitly retracts the incorrect conclusion merged in PR #12: the earlier 40-dps Rayleigh quotient at level 5 mixed the A1 ground state with the almost-degenerate E pair. The resulting level-5/6 difference and the reported fall of the quadratic ratio were not the A1-root data.

There are two equivalent boundary conventions in the two scalar scripts. The standalone script stores the retained-corner diagonal before subtracting `lambda`; its boundary matrix is `T_m(lambda)`, and the final A1/E equations are `alpha+2 beta-lambda=0` and `alpha-beta-lambda=0`. The `schur_decimation.py` convention stores the ordinary Schur complement of `Q_m-lambda I`, so its boundary matrix is `S_m(lambda)=T_m(lambda)-lambda I_3` and its equations are `a_m+2b_m=0` and `a_m-b_m=0`. This is only a scalar shift of the retained 3x3 boundary block; the off-diagonal parameter is identical.

The two update conventions were checked locally at `lambda=1.234, 1.309, 1.411` through twelve gluing steps: `alpha_m-lambda=a_m` and `beta_m=b_m` at every tested step. The uploaded standalone program ran with mpmath 1.3.0 at 260 decimal digits and reproduced the displayed A1 roots for levels 3–9, increments through 8→9, and the E/A1 splitting through level 7. Runtime was approximately 1.6 seconds in the local environment.

An independent 1,250-dps evaluation of the ordinary Schur recursion reproduced the level-12 A1 increment `1.15866956222472296571000231092429262929e-1163`, the level-11 E/A1 splitting `1.73800434333708444856500346638643894393e-1163`, and the stable displayed coefficient `0.4939504899001989528562882796535409482107481...`. The E/A1 splitting divided by the square of the preceding splitting stabilizes near `0.3293003266...`; the ratio of the A1 and E splitting coefficients is 3/2 at the displayed precision.

The outward-rounded interval/inertia check was also repeated locally at 2,450 decimal digits with radius `10^-2390`: all 24 certificates (A1 and E, levels 1–12) passed; all endpoint signs, derivative signs, opposite-channel signs, and midpoint-pivot lower bounds were strict; the minimum midpoint-pivot lower bound was greater than `1.151628330238438...`. This remains a finite-level computer-assisted result. It does not prove convergence as the level tends to infinity, the quadratic law for all levels, or a closed form for the limiting value.


## 39. Standalone Schur-root script precision guard and regression tests (2026-11-06)

The compact 260-dps script now computes the A1 sequence through level 9 and the E sequence only through level 7, which is the range actually tabulated in `HIGH_PRECISION_2026-11-06.md`. The E/A1 splitting at level 9 is about `4.7e-291`, below 260 decimal digits; the previous script calculated E roots through level 9 without displaying them, so it could silently ask Newton continuation to resolve a quantity beyond its precision. This unused calculation is removed rather than presented as a computed value.

The standalone routine was factored as `compute_roots` so the two normalization conventions can be tested directly. The new `test_schur_bottom_eigenvalue.py` checks `T_m(lambda)=S_m(lambda)+lambda I_3` at levels 0, 1, 3, 6, 9, and 12 and three spectral parameters, reproduces the level-9 A1 root and increment coefficient, verifies the E/A1 splittings through level 7, and guards the level-range input. A local isolated run of this test module passed all 21 cases.


## 40. Differentiated A1 Schur update and derivative convergence diagnostics (2026-11-06)

Write the A1 characteristic as `f_m=a_m+2b_m` and set
`c_m=2a_m+lambda-b_m`. The exact one-step identity from Section 35 is
\[
f_{m+1}=f_m-2b_m R_m,
\qquad
R_m=\frac{c_m+5b_m}{c_m+3b_m}.
\]

Differentiating with respect to the spectral parameter (primes denote this derivative) gives
\[
R'_m=\frac{2(c_m b'_m-b_m c'_m)}{(c_m+3b_m)^2},
\qquad c'_m=2a'_m+1-b'_m,
\]
and therefore the exact derivative update
\[
f'_{m+1}
=f'_m-2b'_m\frac{c_m+5b_m}{c_m+3b_m}
-4b_m\frac{c_m b'_m-b_m c'_m}{(c_m+3b_m)^2}.
\]

This identity was checked independently against the existing forward-mode derivative implementation at 39 parameter/level pairs (levels 0–12 and lambda = 1.234, 1.309, 1.411) at 1,000 decimal digits. The largest observed discrepancy was below `2.38e-1001`. A new ordinary regression test now checks the differentiated update at the same 39 points at 100-dps working precision. The test is an implementation consistency check, not a proof of convergence.

At the A1 roots, a separate 10,000-dps calculation gives the following derivative values and successive root-sampled differences:

| m | `D_m=f'_m(lambda_m)` | `D_(m+1)-D_m` |
| ---: | ---: | ---: |
| 5 | -1.2932897430304525953050491537807371… | 1.48044087197e-17 |
| 6 | -1.2932897430304525805006404340445789… | 2.14274337393e-35 |
| 7 | -1.2932897430304525805006404340445789… | 1.98274217145e-71 |
| 8 | -1.2932897430304525805006404340445789… | 8.01146709379e-144 |
| 9 | -1.2932897430304525805006404340445789… | 6.35950828230e-289 |
| 10 | -1.2932897430304525805006404340445789… | 1.97623585730e-579 |
| 11 | -1.2932897430304525805006404340445789… | 9.47707172708e-1161 |
| 12 | -1.2932897430304525805006404340445789… | 1.08602117041e-2323 |
| 13 | -1.2932897430304525805006404340445789… | 7.11868328265e-4650 |
| 14 | -1.2932897430304525805006404340445789… | — |

The corresponding sampled derivative tends numerically to
`-1.293289743030452580500640434044578900991030728263697…`.
The derivative coefficient `b'_m` is also observed to decay: at the A1 root its magnitude is approximately `3.56e-4650` at level 13 and `7.64e-9303` at level 14.

These are high-precision diagnostics only. They do not prove that the derivative sequence converges. In particular, `D_(m+1)-D_m` combines the level update and the change from `lambda_m` to `lambda_(m+1)`. The next proof obligation is a uniform summable bound for the derivative update terms (including `b'_m`) and a separate bound for the derivative's change across the root interval. Only then can the nonzero limiting derivative needed for the quadratic root-shift law be concluded.


## 41. Interval control of the A1 derivative across successive roots (2026-11-06)

Let D_m=f'_m(lambda_m). Differentiating the exact scalar Schur update gives
\[
G_m:=f'_{m+1}(\lambda_m)-f'_m(\lambda_m)
=-2b'_m R_m-2b_mR'_m,
\]
where
\[
R_m=\frac{c_m+5b_m}{c_m+3b_m},\qquad
R'_m=\frac{2(c_mb'_m-b_mc'_m)}{(c_m+3b_m)^2}.
\]
The remaining root-motion term is
\[
f'_{m+1}(\lambda_{m+1})-f'_{m+1}(\lambda_m)
=f''_{m+1}(\xi_m)(\lambda_{m+1}-\lambda_m)
\]
for some xi_m in the interval between the two roots.

A new outward-rounded interval checker propagates second lambda derivatives through the exact rational Schur recursion. It brackets each A1 root at 10,000 decimal digits with radius 10^-9400, checks endpoint signs and a negative first derivative, and verifies all midpoint pivots and the E-channel sign. For every transition m=5,...,13, it evaluates the second derivative over an interval containing the entire segment [lambda_m, lambda_(m+1)]. The certified curvature enclosure lies inside
\[
-0.29<f''_{m+1}(x)<-0.07.
\]

The same interval run certifies, for each m=5,...,13,
\[
\frac{|G_m|}{2^m|b_m|}<0.7,\qquad
\frac{|D_{m+1}-D_m|}{2^m|b_m|}<1,\qquad
\frac{|b_{m+1}|}{|b_m|^2}<0.8.
\]
The largest upper bounds reported were approximately 0.6187181, 0.6187729, and 0.7638668. The root-sampled curvature tends numerically to
\[
-0.283520408592536398378348378958136777568\ldots
\]
but this displayed value is a numerical diagnostic; the interval claim is the coarser bound on the full root-to-root segment.

The reproducible command is
`python computational/spectral_gap_theta_2pi/schur_derivative_certificate.py --max-level 14 --start-level 5 --dps 10000 --radius-digits 9400`.
The regression suite includes a lower-precision smoke test of the interval certificate. A separate GitHub Actions workflow runs the 10,000-dps certificate on the research branch and uploads its log.

The finite-level estimates point to a clean convergence route. If the three bounds above are established uniformly for all m>=6, then |b_6|<10^-36 and |b_(m+1)|<=|b_m|^2 imply
[
sum_{m=6}^{infty}2^m|b_m|
lerac{64cdot10^{-36}}{1-2cdot10^{-36}}
<6.41cdot10^{-35}.
]
Combined with |D_(m+1)-D_m|<=2^m|b_m|, this would prove convergence of D_m and keep its limit separated from zero. What remains is a proof that these estimates persist for every level, not just the finite transitions through level 14.


## 42. Common A1 bootstrap-window interval experiment through level 101 (2026-11-06)

Added `computational/spectral_gap_theta_2pi/schur_bootstrap_box_iv.py` and the focused
`test_spectral_schur_bootstrap_box.py`. This is a new finite interval experiment, separate from the
earlier root-to-root derivative certificate.

The script first continues the scalar A1 boundary root to level 6 at 180-digit working precision.
It then fixes a single asymmetric parameter window
`[lambda_6 - 10^-140, lambda_6 + 1.1·10^-36]` and propagates the exact three-corner Schur recursion
and its first two spectral-parameter derivatives through that same window. Every arithmetic
operation in the interval pass uses `mpmath.iv` outward rounding.

The independent rerun in this session produced the level-6 root candidate

`1.3091289202808134218886230881708101876507678031080187683328996930708725974720891…`.

At the two fixed endpoints, the level-6 A1 characteristic has interval signs

- left endpoint: `+1.2932897430304525804499726533458583·10^-140`;
- right endpoint: `-1.4226187173334978385507044774490368·10^-36`.

The same endpoint sign pattern was verified for every level from 6 through 101. On the whole
parameter window, at each of those finite levels, the interval recurrence also verifies:
- `a_m` lies in `[-10^-35,10^-35]` and `b_m` lies in `[-6·10^-37,0]`;
- `a'_m` and the A1 derivative lie in `[-1.294,-1.292]`;
- `b'_m` lies in `[-1.1·10^-35,1.1·10^-35]`;
- `a''_m` and the A1 second derivative lie in `[-0.286,-0.281]`;
- `b''_m` lies in `[-2.1·10^-34,2.1·10^-34]`;
- every midpoint pivot interval used in the recursion is strictly positive.

The minimum lower endpoint among the current midpoint-pivot eigenvalue intervals is
`1.30912892028081342188862308817081018318197512497465735869384…`.
For each step 6–100, the interval ratio
`(c-b)/(c(c+3b)) = |b_(m+1)|/|b_m|^2` is positive and below 0.8; the largest upper endpoint
is `0.763866709006394859550664540131484644804630685074122411193022…`.

Because the A1 derivative is strictly negative throughout the common interval and the endpoint
signs are opposite, each finite-level A1 characteristic has exactly one zero in that interval.
This is a finite-level statement for the continued A1 boundary characteristic. It does not extend
the separate global spectral-order/inertia certification beyond level 12.

The script reports a conditional all-future root-shift budget of
`9.28792569659442724458·10^-37`. This budget assumes that the finite bootstrap inequalities,
including the 0.8 contraction, persist at every future level. It is a conditional estimate, not a
certificate that the bootstrap box is invariant for all levels.

Local verification:
`python -m pytest -q test_spectral_schur_bootstrap_box.py` — 1 passed in 8.85 s.
The direct run
`python computational/spectral_gap_theta_2pi/schur_bootstrap_box_iv.py --max-level 101 --dps 180 --radius-digits 140`
reproduces the figures above.

The next mathematical obligation is now sharper: prove the coarse bootstrap region is invariant
under the differentiated Schur map, rather than merely checking a long finite orbit. The Lean
lemma added alongside this experiment proves the one-step four-fifths off-diagonal contraction
under the coarse pivot/sign box assumptions; it does not prove those assumptions remain invariant.



## 43. Signed one-step invariance of the small off-diagonal interval (2026-11-06)

After the one-step Lean contraction theorem was checked by the complete
`lake build PhiGenesis` workflow on the preceding source revision, the off-diagonal
estimate was strengthened in two ways.

First, combining
`schurNextOffDiagonal_abs_le_six_e_minus37_of_box` with the existing
`schurNextOffDiagonal_neg` sign lemma (and handling `b=0` separately) gives

`-6e-37 <= b_next <= 0`

whenever the coarse pivot hypotheses hold and `b` already belongs to
`[-6e-37,0]`. This is the signed interval statement, not only an absolute-value
bound.

Second, `schurNextOffDiagonal_signed_interval_of_state_box` derives the coarse
pivot hypotheses from the state-coordinate assumptions

- `-1e-35 <= a <= 1e-35`;
- `-6e-37 <= b <= 0`;
- `1309/1000 <= lambda <= 131/100`.

Indeed, with `c=2a+lambda-b` and `c+3b=2a+lambda+2b`, these hypotheses imply
`13/10 <= c <= 132/100` and `13/10 <= c+3b`; the previously proved
off-diagonal contraction then gives the signed interval at the next Schur step.

The parameter interval `[1.309,1.31]` is an explicit hypothesis of this generic
Lean implication. It is not yet a Lean theorem about the level-6 root or about every
subsequent root. Likewise, the current proof does not establish preservation of the
`a`, first-derivative, or second-derivative coordinates. Consequently this is a
conditional one-step closure of the signed `b`-coordinate only, not an all-level
bootstrap theorem.

The remaining induction work is now localized: prove compatible propagation bounds for
`a`, `a'`, `b'`, `a''`, and `b''`, and separately justify the spectral-parameter
window in Lean. The finite interval calculation through level 101 remains numerical
evidence for the hypotheses, rather than a proof that those hypotheses persist at all
levels.


## 44. Diagonal-coordinate Schur drift estimate (2026-11-06)

The diagonal update was read directly from the implementation
`schurNextDiagonal a b c = a - 2*b^2*(c+b)/(c*(c+3*b))`
and formalized without a numerical approximation.

Under
`-1/100 <= b <= 0`,
`13/10 <= c <= 132/100`, and
`13/10 <= c+3*b`,
the numerator `c+b` is nonnegative and at most `132/100`, whereas
the denominator `c*(c+3*b)` is at least `(13/10)^2`. Since
`132/100 <= (13/10)^2`, the update fraction lies in `[0,1].
Consequently Lean proves

`|schurNextDiagonal a b c - a| <= 2*b^2`.

A state-box corollary takes
`|a| <= 10^-35`,
`b in [-6*10^-37,0]`, and
`lambda in [1.309,1.31]`; as in the previous signed off-diagonal result,
the lambda interval is an explicit hypothesis. It derives the midpoint-pivot
bounds and proves the numerical one-step drift estimate

`|a_next-a| <= 72*10^-74 = 7.2*10^-73`.

This does not yet prove that the whole `a in [-10^-35,10^-35]` box is
invariant: a uniform interval argument must account for the current value's
interior margin (or sharpen the box). What is now proved is that each local
diagonal increment is bounded by twice the square of the old off-diagonal
coefficient. The next step is to combine this inequality with an all-level
bound on the `b`-sequence to obtain a rigorous summable drift estimate.

The result is conditional on the same finite-dimensional state and spectral
parameter hypotheses; it is not an infinite-level convergence theorem.


## 45. Linear contraction of the off-diagonal coordinate (2026-11-06)

The quadratic estimate from section 43 gives
`|b_next| <= (4/5)|b|^2`. On the signed state interval
`-6*10^-37 <= b <= 0`, one has
`|b| <= 6*10^-37`. Thus

`(4/5)|b|^2 <= ((4/5)*(6*10^-37))|b| < 10^-36|b|`.

This exact rational comparison is now formalized in
`schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_box`.
A state-coordinate corollary,
`schurNextOffDiagonal_abs_le_e_minus36_mul_abs_of_state_box`,
derives the positive midpoint-pivot bounds from
`|a| <= 10^-35`,
`b in [-6*10^-37,0]`, and
`lambda in [1.309,1.31]`.

The result provides a conditional geometric one-step factor
`q=10^-36`. If the state and spectral-parameter hypotheses are established
at every subsequent level, then `|b_(m+n)| <= q^n |b_m|`.
The all-level validity of those hypotheses remains a separate theorem;
this section does not claim to have proved it.

The next formal task is a finite-sum/tail lemma for the diagonal drift
`|a_(k+1)-a_k| <= 2|b_k|^2` under the geometric bound, with the resulting
explicit total tail estimate. That summability estimate will then be used
to sharpen the diagonal state interval rather than assuming an arbitrary
fixed margin.


## 46. Finite geometric summation of the diagonal drift (2026-11-06)

Added the abstract Lean theorem
`sum_sq_le_two_mul_initial_sq_of_half_contraction`. Its hypotheses are
`0 <= u_n` and `u_(n+1) <= (1/2)u_n`. By induction,
`u_n <= u_0(1/2)^n); an explicit finite geometric-tail invariant proves
`sum_{k<N}(1/4)^k <= 2). Hence

`sum_{k<N}u_k^2 <= 2u_0^2`.

The companion theorem
`diagonal_drift_total_le_four_mul_initial_sq` assumes the local bounds
`|a_(n+1)-a_n| <= 2u_n^2` and concludes

`|a_N-a_0| <= 4u_0^2`.

This is a finite and abstract summation statement. It does not assume or
prove the Schur state-box induction. The previously derived Schur factor
`10^-36` implies the required half-contraction whenever its state and
parameter hypotheses are valid at each step. Establishing those hypotheses
for every step, including the root window and the diagonal coordinate, is
still the outstanding bootstrap task.


## 47. Finite-horizon drift estimate with prefix-only hypotheses (2026-11-06)

Section 46 gave the abstract finite sum and drift estimate, but its Lean
interface quantified the contraction and diagonal-step assumptions over
all natural numbers. That interface is stronger than needed for a proof
about a fixed finite Schur-recursion prefix and obscures the induction
boundary.

Added the theorem diagonal_drift_total_le_four_mul_initial_sq_until.
Its assumptions are now restricted to the finite prefix:

- 0 <= u_n for n <= N;
- u_(n+1) <= (1/2) u_n for n < N;
- |a_(n+1)-a_n| <= 2*u_n^2 for n < N.

The proof defines a zero extension of u after N and a constant
extension of a after N, then applies the already checked all-index
summation theorem. This avoids assuming or referring to any values of the
original sequences beyond the endpoint.

The numeric corollary
diagonal_drift_total_le_144_e_minus72_until adds only
u_0 <= 6*10^-37 and concludes

|a_N-a_0| <= 4*(6*10^-37)^2 = 1.44*10^-72.

This is the quantitative margin budget for the diagonal coordinate on
any finite prefix. It is much smaller than the 10^-35 state-box width.
The estimate is conditional on the local contraction and diagonal-step
bounds along that prefix; it does not itself prove the state-box hypotheses.

The next proof step is to use this prefix-only theorem inside a simultaneous
induction for the concrete Schur sequences (a_n,b_n) at a fixed parameter
in [1.309,1.31]. The induction needs a separately certified initial
diagonal margin at level 6, the signed initial b interval, and the
one-step Schur update identities. The spectral parameter window must still
be justified for the intended A1 root; no infinite-level limit is claimed
by this finite-prefix lemma.

## 48. Sharpened level-six diagonal start box (2026-11-06)

The common-window interval calculation was inspected at its starting level
rather than only recording the wider invariant box used in the subsequent
finite propagation. With the same outward-rounded parameter interval

[lambda_6 - 10^-140, lambda_6 + 1.1*10^-36]

the level-six diagonal coefficient is enclosed by

a_6 in [-1.6514094855799782169601637221860967e-36,
          2.5607381821932903298469192438172193e-36].

Thus |a_6| < 3*10^-36, while the existing level-six off-diagonal
certificate gives b_6 in [-6*10^-37,0]. The fixed parameter interval is
strictly inside the coarse rational window [1.309,1.31].

The bootstrap script now returns the outward-rounded level-six diagonal
endpoints, fails if they leave [-3e-36,3e-36], and the regression test
checks both endpoints and the inclusion of the fixed parameter window in
[1.309,1.31].

The Lean lemma
schurDiagonal_abs_le_e_minus35_of_initial_three_e_minus36_and_drift
combines this sharpened start bound with the finite-prefix drift budget
1.44e-72 to recover |a_m| <= 1e-35. This gives a quantified numerical
margin for the planned simultaneous state induction. It does not yet
prove the all-level induction itself or the root-window endpoint signs
inside Lean.

## 49. Conditional all-level invariance of the two Schur state coordinates (2026-11-06)

Added an explicit fixed-parameter trajectory constructor and the theorem
`schurBoundaryTrajectory_state_box`. Its hypotheses are a fixed rational
spectral window `lambda in [1.309,1.31]`, a starting diagonal value
`|a_0| <= 3e-36`, and a starting signed off-diagonal value
`b_0 in [-6e-37,0]`.

The proof is a simultaneous induction over the concrete Schur update.
At each prefix it derives the half-contraction of `|b_n|` from the existing
stronger `1e-36` one-step factor, derives the exact diagonal increment
`|a_(n+1)-a_n| <= 2|b_n|^2`, and applies the prefix-only drift theorem.
The total diagonal displacement is bounded by `1.44e-72`; combined with
the initial `3e-36` margin this preserves `|a_n| <= 1e-35`. The signed
off-diagonal interval is preserved by the existing Schur sign/contraction
lemma. Thus the state coordinates are now genuinely invariant for every
finite index, not merely checked through level 101.

Scope remains conditional: this theorem assumes the fixed parameter
window and the level-six starting state enclosure. It does not yet prove
that the actual A1 root belongs to that window, establish the common
window endpoint signs for all levels, or prove convergence of the
root-sampled derivative. Those are the remaining spectral steps.


## 50. One-step A1 characteristic drift inside the invariant state box (2026-11-06)

Added the Lean theorem schurNextA1_increment_bounds_of_state_box.
For a and b in the established invariant state box and lambda >= 1.309,
the exact characteristic update is
f_next - f = (-2*b) * (lambda + 2*f) / (lambda + 2*f - 2*b),
where f = a + 2*b. The positive numerator and denominator, together
with b <= 0, put the quotient in (0,1]. Lean therefore proves
0 <= f_next-f <= 2*(-b) = 2*|b|.

This is the next missing bridge from state-coordinate invariance to a
common endpoint-sign argument. The lower endpoint sign is monotone under
the recurrence. For the upper endpoint, the increments must be summed;
the existing 10^-36 contraction gives a much sharper budget than the
coarser half-contraction. The finite sum and endpoint initial signs have
not yet been combined into an all-level A1 root bracket.


## 51. All-finite-level transport of the A1 endpoint signs (2026-11-06)

Added a finite geometric-sum theorem for any nonnegative sequence with
quarter-contraction:
`sum_{k<N} u_k <= (4/3) u_0`. The proof uses a tail-preserving induction,
not an infinite-series argument.

Combined with the conditional Schur state-box theorem and the exact
one-step A1 increment formula, the new trajectory lemmas establish:

- If the initial A1 characteristic is nonnegative, it remains
  nonnegative at every finite Schur level.
- If the initial A1 characteristic is at most `-17e-37`, it remains
  at most `-1e-37` at every finite level.

For the upper endpoint, the argument uses the already-proved
`10^-36` off-diagonal linear contraction, weakens it to a factor
`1/4`, and obtains
`2 * sum_{k<N}|b_k| <= (8/3)|b_0| <= 16e-37`.
The initial margin is `17e-37`, leaving a strict negative margin
`1e-37`. The lower endpoint follows from monotonicity of the A1
characteristic.

This closes the all-finite-level endpoint-sign transport **conditional on
the exact level-six endpoint state and characteristic inequalities**.
It does not yet prove those rational start inequalities in Lean, establish
continuity/root existence for every level, or prove convergence of the
root sequence. The next proof obligation is the exact rational level-six
endpoint certificate.


## 52. Exact rational level-six endpoint certificates (2026-11-06)

The narrow common parameter interval is now represented by two exact
rationals in Lean:
- L = 1309128920280813421888623088170810187 / 10^36;
- U = 1309128920280813421888623088170810189 / 10^36.

Both are proved to lie in [1.309,1.31]. The new theorems
`schurBootstrapLower_levelSix_certificate` and
`schurBootstrapUpper_levelSix_certificate` unfold the exact three-corner
Schur recurrence for six steps, starting from the original state
(a,b)=(2-lambda,1). They establish at each endpoint:
`|a_6| <= 3e-36` and `-6e-37 <= b_6 <= 0`.
The lower endpoint has `f_6(L)>0); the upper endpoint has the stronger
margin `f_6(U)<=-17e-37`.

This removes the floating-point/interval-computation starting-state
assumption at the two rational endpoints. Combined with Section 51, it
will give exact opposite A1 signs at every finite level at L and U.
It still does not show a uniform state enclosure for every lambda in the
entire interval, prove continuity of the level-n characteristic there,
or prove root existence and convergence. Those form the next analytic
bridge.


## 53. Exact opposite A1 endpoint signs at every finite level (2026-11-06)

Added `schurBootstrapEndpoints_A1_signs_all_finite_levels`, which applies
the exact rational level-six certificates from Section 52 to the
conditional trajectory sign-transport results from Section 51.

For the fixed rational lower endpoint L, the A1 characteristic is
nonnegative at every finite level. For the fixed rational upper endpoint
U, it remains strictly negative at every finite level. The proof uses
only exact Lean theorems: the rational endpoint bounds, the six-step
Schur certificates, state-box invariance, the one-step A1 increment
bound, and the finite quarter-geometric sum. It does not use numerical
interval output as a proof premise.

This establishes the two-endpoint sign part of the common bracket.
The next missing condition for an intermediate-value argument is a
uniform state/pivot bound for all lambda in [L,U], so that each finite
level characteristic is continuous on that interval. Root existence at
each finite level and convergence remain open.


## 54. Finite-level continuity of the Schur characteristic (2026-11-06)

Added two local continuity lemmas for the rational diagonal/off-diagonal
Schur updates and an induction theorem
schurBoundaryTrajectory_pair_continuousAt_of_nonzero_pivots.
For the original parameterized initial state (2-lambda, 1), both
coordinates at level n are continuous at a fixed lambda₀ whenever the
two scalar denominators c and c+3b are nonzero at every preceding
step k<n. Consequently,
schurBoundaryTrajectory_A1_continuousAt_of_nonzero_pivots proves
continuity at that parameter for the finite-level A1 characteristic.

This is a genuine analytic lemma, but its premise is pointwise
nonvanishing along the finite trajectory. It does not establish
nonvanishing uniformly for every lambda in the narrow interval
[L,U], and it does not yet infer a root from the endpoint signs.
The next required bridge is a verified finite-prefix denominator bound
on the whole parameter interval, followed by the interval-closed
continuity/IVT argument. The infinite-level root convergence problem
remains open.


## 55. Conditional finite-level root existence by IVT (2026-11-06)

Added the level-index semigroup identity for the Schur trajectory and
defined schurBootstrapA1AtLevel for the original recursion at level 6+n.
Using the already-proved opposite signs at the exact rational endpoints,
the new theorem schurBootstrapA1AtLevel_exists_root_of_nonzero_pivots
applies the closed-interval intermediate value theorem: for each finite
n, if both Schur denominators remain nonzero along the trajectory for
every parameter in [L,U] through level 6+n, then the level-(6+n) A1
characteristic has a zero in [L,U].

The premise is deliberately explicit. The pointwise continuity induction
from Section 54 supplies continuity once these denominators are known to
be nonzero, but a uniform proof of that nonvanishing over [L,U] is not
yet in the file. Thus this theorem is the IVT bridge, not yet an
unconditional finite-level root-existence theorem. Uniform initial
level-six state enclosure and the finite prefix pivot check remain the
next obligations; convergence of the roots is still separate.
