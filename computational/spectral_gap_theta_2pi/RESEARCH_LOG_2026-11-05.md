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

- \`.github/workflows/lean.yml\` watches Lean sources, \`lakefile.lean\`, \`lean-toolchain\`, and itself; it does not watch \`computational/**\`.
- \`.github/workflows/tests.yml\` runs only on pushes to \`main\` and pull requests targeting \`main\`.
- The 4472ddba commit changed only this research log and the Python audit script. Therefore neither existing workflow was eligible to run.

The first audit script also had a weak holonomy assertion: it multiplied a constant expression rather than looking up the three signs stored for each face. The revised script now computes the signed product from the actual edge-sign table.

### Checks rerun in the sandbox

1. Exact face/sign audit, levels 0--10:
   - \`|F_m|=3^m\`, \`|E_m|=3^{m+1}\`, and \`|V_m|=(3^{m+1}+3)/2\`.
   - Every edge belongs to exactly one elementary face.
   - Every vertex belongs to one or two elementary faces.
   - The gauge identity \`s_uv = epsilon(u) epsilon(v)\` holds on every edge.
   - The repository-sign convention \`sigma=-s\` has product \`-1\` around every elementary upward face.

2. Direct graph comparison against \`phi_genesis.sg_laplacian.sierpinski_graph\`, levels 0--8: vertex and edge sets agree exactly after conversion to integer triangular-lattice coordinates.

3. Lowest eigenvalue of the local-face operator \`L=D-A_sigma\`, with \`sigma=-s\`, levels 1--8:
   \`1.17157287525381, 1.29843788128358, 1.30907106525561, 1.30912891862700, 1.30912892028081, 1.30912892028081, 1.30912892028081, 1.30912892028082\`.
   These are floating-point sparse-eigensolver outputs. They reproduce the earlier table; they are not the proof of the lower bound.

### Crucial comparison with the existing hole-flux solver

The default \`phi_genesis.mobius.mobius_spectrum\` representative solves one parity-one equation for every listed hole and sets free variables to zero. The local-face assignment instead sets the GF(2) variable to one on each horizontal \`(a,b)\` face edge and zero on the other two face edges.

For levels 1--6, the local-face assignment has parity zero on every listed hole row, while the default solver requires parity one on every such row. The two representatives differ on 2, 8, 26, 80, 242, and 728 edges, respectively. Their smallest eigenvalues are:

| level | pivot-zero all-hole representative | local-face representative |
|---:|---:|---:|
| 1 | 0.330920911718 | 1.171572875254 |
| 2 | 0.374778207648 | 1.298437881284 |
| 3 | 0.454116460742 | 1.309071065256 |
| 4 | 0.459731121824 | 1.309128918627 |
| 5 | 0.459731877707 | 1.309128920281 |
| 6 | 0.459731877707 | 1.309128920281 |

Consequently, the bound \`lambda_min >= 1\` is a result for the local-face signing, not for the default all-hole-flux calculation already documented in \`mobius.py\`. The two matrices have different elementary/hole cycle data and must not be described as gauge-equivalent. The theta = 2 pi label remains conditional until the original external \`sg.py\` and \`gap.py\` are inspected.

## 9. Reproducible automation and next steps

A dedicated workflow, \`.github/workflows/spectral-gap-theta2pi.yml\`, now runs this audit on pushes to \`formalize/h10-lean4\` that touch the spectral-gap audit, the recursive graph builder, or the hole-flux implementation. It runs four checks: exact face/gauge data through level 10, direct graph comparison through level 8, local-face eigenvalues through level 8, and local-face versus pivot-zero hole-solver comparison through level 6.

Next:
1. Obtain the original external \`sg.py\` and \`gap.py\`; verify that their face ordering, edge signs, and matrix convention are exactly this local-face operator before treating the theta label as identified.
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