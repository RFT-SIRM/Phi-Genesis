# H10 canonical pivot-zero recurrence — audit and proof program

**Date:** 5 November 2026  
**Target:** the scalar signed-\(\mathbb Z_2\)-flux Laplacian in phi_genesis/higher_moments_z2.py  
**Branch:** formalize/h10-pivot-zero-invariant  
**Status:** Phase 0 audit. The finite checks below are reproduced; the all-level mathematical checkpoint is recorded; the complete recurrence is **not yet a Lean-kernel theorem**.

This note is the current status boundary for the pivot-zero H10 work. It does not alter the operator, edge ordering, canonical solver, or the statement of the proposed recurrence.

## 1. Exact target and meaning of the result

For level \(m\), let \(B_m\) be the hole-boundary incidence matrix over \(\mathbb F_2\), with rows indexed by ternary addresses and columns indexed by the repository's sorted primal edges. Let \(b_m(t)\) be the prescribed generation-parity right-hand side. The repository chooses the deterministic solution
\[
\sigma_m(t)=\text{the solution of }B_m x=b_m(t)
\text{ with every non-pivot variable set to }0,
\]
using the pivot convention implemented by PackedGF2System. Define the signed integer Laplacian
\[
L_m(t)=\operatorname{Deg}_m-A_{\sigma_m(t)}
\]
and
\[
F_m(t_1,\ldots,t_m)=\operatorname{Tr}(L_m(t)^{10}).
\]

The all-mask recurrence stated in the 4 November mathematical checkpoint is
\[
F_{m+1}(t_1,\ldots,t_m,d)
=3F_m(t_1,\ldots,t_m)+Q(t_1,t_2,t_3,d),
\qquad m\ge 3,
\]
where, writing \(a=t_1,\ b=t_2,\ c=t_3\),
\[
\begin{aligned}
Q(a,b,c,d)={}&127182024+89195520a+73945440b-145153920ab\\
&+55360c-150880ac+40320bc-39680abc\\
&+d(115347760-110022480a+10024960b\\
&\qquad-20854720ab+320c-640ac).
\end{aligned}
\]

For the full-flux defect
\[
D_m^{(10)}=F_m(1,\ldots,1)-F_m(0,\ldots,0),
\]
the stated consequence is
\[
D_{m+1}^{(10)}=3D_m^{(10)}+12387360,\qquad m\ge3,
\]
with
\[
D_m^{(10)}
=555046440\cdot3^{m-3}-6193680,\qquad m\ge3.
\]
The proposed normalized limit is
\[
\lim_{m\to\infty}\frac{D_m^{(10)}}{|V_m|}
=\frac{370030960}{27},
\qquad |V_m|=\frac{3^{m+1}+3}{2}.
\]

The precise claim is therefore about the repository's **canonical pivot-zero representative and its fixed edge order**. It is not a claim that the increment \(12387360\) is shared by every signing with the same hole-boundary parities.

## 2. Three different notions that must not be conflated

1. **Vertex-switching invariance.** If \(S=\operatorname{diag}(\epsilon_v)\), \(\epsilon_v\in\{-1,+1\}\), then switching sends \(L\) to \(SLS\). Thus \(\operatorname{Tr}((SLS)^{10})=\operatorname{Tr}(L^{10})\). This is a genuine invariant of a switching class.

2. **Hole-parity constraints.** These do not determine a unique switching class in this graph. The 3 November finite audit reports cycle-space rank 364 and hole-boundary constraint rank 121 at level 5, leaving 243 boundary-invisible cycle directions. Its 243 tested flips preserve the prescribed hole parities but change the tenth trace. This is a warning against calling the H10 increment an invariant of hole flux alone.

3. **Canonical pivot-zero response.** The proposed recurrence is tied to the deterministic section selected by the lexicographic edge order and the rule “all non-pivot variables are zero”. Those conventions are part of the theorem statement and must remain fixed throughout the proof.

The scalar signed-\(\mathbb Z_2\) operator in Phi-Genesis is a different mathematical object from the SU(2)-valued operator in Evgeny-Theorem. The formula \(12387360\) belongs to the former; it must not be identified with the conditional SU(2) H10 residual in the latter.

## 3. Independent sandbox checks reproduced on 5 November

The current source was read from main at phi_genesis/higher_moments_z2.py (blob fe14c70846a8508b0a3445c56125223994df2a43). The sandbox did not have a Lean/Lake executable or a working GitHub DNS route, so these were exact Python-level checks, not a local Lean build. The graph, boundary, packed GF(2), and tree-audit procedures were independently reconstructed from the inspected source; the results below must not be described as a run of the repository's full audit bundle.

### 3.1 Canonical pivot/address-tree checks

For each level 1 through 10, the source-level reconstruction checked that:

- the transformed boundary columns have weight at most two;
- the address-parent candidate edges exist and form a connected acyclic tree;
- the candidate tree is the lexicographic greedy spanning tree of the transformed dual multigraph;
- its selected edge IDs equal the packed solver's pivot set;
- the least edge in each tested fundamental cut is the candidate parent edge;
- the closed-form generation-basis assignment satisfies every original boundary equation.

The level counts were:

| Level | Vertices | Primal edges | Hole rows / tree edges | Nonzero dual edges |
|---:|---:|---:|---:|---:|
| 1 | 6 | 9 | 1 | 6 |
| 2 | 15 | 27 | 4 | 18 |
| 3 | 42 | 81 | 13 | 54 |
| 4 | 123 | 243 | 40 | 162 |
| 5 | 366 | 729 | 121 | 486 |
| 6 | 1,095 | 2,187 | 364 | 1,458 |
| 7 | 3,282 | 6,561 | 1,093 | 4,374 |
| 8 | 9,843 | 19,683 | 3,280 | 13,122 |
| 9 | 29,526 | 59,049 | 9,841 | 39,366 |
| 10 | 88,575 | 177,147 | 29,524 | 118,098 |

These are finite checks through level 10. They do not prove the corresponding universal geometric statements.

### 3.2 Reference solver and boundary extraction

The literal geometric boundary scan and dense RREF solver were compared with the inspected optimized implementation for all generation masks at levels 1 through 5 (62 masks total). Every boundary list and every canonical GF(2) solution agreed.

### 3.3 Tenth traces and transition formula

Exact sparse integer traces using
\[
\operatorname{Tr}(L^{10})=\|L^5\|_F^2
\]
were independently recomputed for both untwisted and full-flux masks at levels 1 through 5:

| Level | Untwisted trace | Full-flux trace | \(D_m^{(10)}\) |
|---:|---:|---:|---:|
| 1 | 36,210,078 | 55,733,958 | 19,523,880 |
| 2 | 232,629,318 | 411,403,758 | 178,774,440 |
| 3 | 825,069,618 | 1,373,922,378 | 548,852,760 |
| 4 | 2,602,390,878 | 4,261,336,518 | 1,658,945,640 |
| 5 | 7,934,354,658 | 12,923,578,938 | 4,989,224,280 |

All generation-mask traces were recomputed at levels 3, 4, and 5. For transitions \(3\to4\) and \(4\to5\), all 48 parent-mask/new-bit checks matched the stated \(Q\) recurrence exactly.

The 16 Boolean values of \(Q\) also match Q_truth_table_16.csv. In particular,
\[
Q(0,0,0,0)=127182024,\quad
Q(1,1,1,1)=139569384,
\]
so their difference is exactly \(12387360\).

The tracked CSV full_flux_h10_levels_1_10.csv was separately checked arithmetically: its rows satisfy the stated closed form for levels 3–10 and the residual \(D_{m+1}-3D_m=12387360\) for transitions 3→4 through 9→10. This is a consistency check of the stored rows, not an independent recomputation of the level-6–10 traces in this sandbox.

### 3.4 Checks not independently rerun in this session

The following remain source-reported results, not fresh sandbox reruns here: the complete level-12 face-holonomy sweep, level-12 A/B/C monotonicity sweep, all 243 level-5 boundary-invisible flips, all 496 masks at levels 4–8, and the level-11/12 direct traces. Their existing records remain useful evidence, but this audit does not upgrade them to independently reproduced results.

## 4. Current Lean-kernel boundary

The current main includes a Lean project pinned to leanprover/lean4:v4.33.1 and Mathlib v4.33.1. The merged PR #7 build (42034013690) completed lake build PhiGenesis successfully. That build validates the modules currently imported by PhiGenesis.lean; it does **not** validate the complete H10 recurrence, which is not yet present in the Lean dependency graph.

Already formalized in the imported modules are:

- generic incidence/forest results over ZMod 2, including linear independence iff forest for incidence columns;
- a rank-decreasing parent-map forest and an abstract address-tree solver specification;
- injectivity of the triangular boundary-row transform on finite address levels;
- exact integer child embeddings and pairwise child-intersection geometry;
- the recursive first-occurrence vertex list, membership and nodup properties, and the child-0 prefix result;
- an abstract A/B/C six-vertex automaton;
- a concrete state-A sublist and the A-parent child realization A/A/B.

The abstract A/B/C automaton explicitly does not, by itself, identify its symbols with the actual first-occurrence IDs of every recursive cell. The current concrete realization is limited to the state-A parent and its A/A/B children.

## 5. Remaining theorem dependencies

The following are separate proof obligations. A finite audit or an abstract helper theorem must not be counted as a substitute for its concrete all-level link.

| Order | Obligation | Required output |
|---:|---|---|
| 1 | Concrete B/C cell-state realization | Derive the B/C six-vertex orders from the actual first-occurrence list at arbitrary addresses, not just the abstract transition function. |
| 2 | Side/hypotenuse monotonicity and sorted edge order | Prove that the recursive vertex IDs induce the exact lexicographic edge list used by the graph constructor. |
| 3 | Concrete transformed columns | Define the actual hole-boundary matrix and row transform; prove each edge column has 0, 1, or 2 ones and retain parallel dual edges correctly. |
| 4 | Fundamental-cut geometry | Identify the actual address-tree component after deleting each parent edge; prove the internal and terminal cut-row formulas for the real boundary rows. |
| 5 | Least-edge theorem and canonical pivot set | Prove that the least actual primal-edge index in every concrete cut is exactly its address-parent edge; connect the resulting tree to the exact solver's pivot convention. |
| 6 | Cocycle restriction and switching | Prove the face-holonomy basis, child restriction laws up to vertex switching, and conjugation invariance for the diagonal moments used in gluing. |
| 7 | Uniform local H10 correction | Formalize the radius-4 corner patch and two-edge defect patch with full external degrees on diagonals; verify the local moments and Boolean Q table in Lean. |
| 8 | Trace gluing and base transition | Prove the ordered length-10 three-copy decomposition, coefficient 10/r, and the exact 3→4 bridge for all 16 Boolean patterns. |
| 9 | Final assembly | Combine the previous results into the arbitrary-mask recurrence, then derive the full-flux recurrence, closed form, and normalized limit. |

The first five obligations complete the concrete canonical GF(2) pivot-zero theorem. Obligations 6–9 connect that solution to the tenth trace. Both layers are necessary for the requested invariant.

## 6. Implementation order

1. Keep the Python graph constructor, sorted edge order, canonical solver, and non-pivot-zero convention unchanged.
2. Finish the concrete B/C realization from the existing A-state and child-cell lemmas. Do not generalize the abstract automaton in place of this realization.
3. Formalize the exact vertex-ID-to-sorted-edge order, then instantiate transformed boundary columns as a concrete dual multigraph.
4. Prove the actual cut components and least-edge theorem, including the terminal v(w) case.
5. Connect the address-tree formula to the packed solver's exact pivot convention and derive the canonical generation solution for every mask by linearity.
6. Prove switching-class child restrictions and the radius-4 locality statement.
7. Formalize the exact patch moments and ordered three-copy trace gluing; preserve matrix-factor order and multiplicities.
8. Close the 16-case 3→4 base transition and assemble the all-mask recurrence.
9. Derive the full-flux affine recurrence, closed form, and normalized limit only after the all-mask theorem compiles.

Each stage is accepted only on a clean exact-SHA lake build PhiGenesis. No sorry, admit, new axioms, unsafe shortcuts, or trusted Python-only constants are permitted in the final theorem.

## 7. CI and branch policy

The prior .github/workflows/lean.yml listened only to pushes on formalize/h10-lean4 and manual dispatch. That would silently omit automatic Lean validation on a newly named formalization branch and on its pull request to main.

This branch updates the workflow to run on pushes under formalize/** and on pull requests targeting main, with the existing Lean build command and pinned toolchain/dependency unchanged. A successful run on the partial current project is still only a successful build of that partial project.

## 8. Source of record

- phi_genesis/higher_moments_z2.py — canonical graph constructor, exact sorted edge order, hole boundaries, packed GF(2) solve, signed Laplacian, and exact trace functions.
- computational/higher_moments_z2/audit_gf2_pivot_tree.py — finite pivot/tree/cut audit.
- computational/higher_moments_z2/GF2_PIVOT_RECURSION_2026-11-04.md — incidence/forest and address-tree reduction.
- computational/higher_moments_z2/H10_ALL_LEVEL_CHECKPOINT_2026-11-04.md — paper-level all-mask recurrence and locality checkpoint; not a Lean proof.
- computational/higher_moments_z2/FOLLOWUP_2026-11-03.md — historical finite mechanism and hole-parity/switching boundary.
- computational/higher_moments_z2/LEAN4_FORMALIZATION_TASK_2026-11-04.md — historical implementation task; its original “no Lean project” baseline has been superseded by the current partial Lean project.
- PhiGenesis/H10/IncidenceForest.lean, BoundaryRowTransform.lean, GasketCoordinates.lean, GasketVertexOrder.lean, GasketVertexGeometry.lean, VertexOrder.lean, GasketVertexStateA.lean, and GasketVertexChildCells.lean — current formalization base.

**Acceptance rule:** do not mark the pivot-zero H10 invariant complete until the concrete canonical-solver theorem and the all-mask tenth-trace recurrence are both available as kernel-checked theorems on an exact green commit.
