# GF(2) pivot-tree recursion for the signed Sierpiński gasket

**Date:** 4 November 2026  
**Scope:** canonical representative produced by PackedGF2System in phi_genesis/higher_moments_z2.py.  
**Status:** the general linear-algebra theorem below is proved. The address-tree description and closed-form solution pass an exact audit through level 10. The remaining all-level geometric edge-order lemma is isolated explicitly. This note does **not** claim an all-level H10 trace recurrence.

## 1. Boundary system and a row transformation

Index holes by ternary addresses
\[
W_m=\bigcup_{j=0}^{m-1}\{0,1,2\}^j,\qquad g(u)=m-|u|.
\]
Write \(B_u\in\mathbb F_2^{E_m}\) for the boundary-edge incidence vector of hole \(u\). A generation mask \(t=(t_1,\ldots,t_m)\) has right-hand side \(b_u=t_{m-|u|}\).

Use the triangular row change
\[
C_u=\begin{cases}
B_u+B_{u0}+B_{u1}+B_{u2},&|u|<m-1,\\
B_u,&|u|=m-1.
\end{cases}\tag{1}
\]
It is invertible: recover \(B_u=C_u\) at leaves, and then recover the remaining \(B_u\)'s upwards by the same relation. Hence it preserves the row space and the pivot-column set.

## 2. General incidence-matrix theorem

**Theorem 1 (canonical solution on the lexicographic dual tree).** Let \(M\) be a matrix over \(\mathbb F_2\), with rows indexed by a finite set \(W\). Suppose every column has 0, 1, or 2 nonzero entries. Construct a multigraph \(D\) on \(W\cup\{R\}\): a column with two ones joins its two row vertices, one one joins that vertex to \(R\), and a zero column is discarded. Assume \(D\) is connected.

Scanning columns in increasing order and retaining a column exactly when it is independent gives the lexicographically first spanning tree \(T\) of \(D\). These retained columns are exactly the pivot columns of row reduction. If all non-tree variables are set to zero, the unique solution of \(Mx=b\) is
\[
x_e=\sum_{v\in K_e}b_v\pmod2,\tag{2}
\]
where \(K_e\) is the component of \(T-e\) not containing \(R\).

*Proof.* In an incidence matrix over \(\mathbb F_2\), a set of columns is independent iff its edges form a forest: a cycle gives a zero sum, and a nonempty forest has a leaf, which rules out a nontrivial dependence. Thus the left-to-right independent-column scan is exactly the greedy spanning-tree algorithm. Invertible row operations preserve the column dependencies and pivot-column set. On the resulting tree, summing the vertex equations over \(K_e\) cancels each internal edge twice and leaves only \(x_e\), giving (2). A tree has no nonzero cycle flow, so the solution is unique. \(\square\)

This theorem is independent of Sierpiński geometry and is the main reusable Lean 4 lemma.

## 3. Address tree observed in the Sierpiński system

For every address \(u\in W_m\), the candidate tree has one edge from \(u\) to
\[
p_m(u)=
\begin{cases}
u0\,1^{m-|u|-2},&|u|<m-1,\\
u_{<r},&|u|=m-1,\ r=\max\{i:u_i=2\}\text{ exists},\\
R,&|u|=m-1\text{ and }u\text{ contains no }2.
\end{cases}\tag{3}
\]
Here \(u_{<r}\) is the prefix strictly before the rightmost digit \(2\). For each pair \(\{u,p_m(u)\}\), take the least-indexed primal edge whose transformed column joins that pair; call it \(e_u\).

The parent rule (3) makes a tree: a nonterminal word maps to a terminal word \(u0\,1^k\); that terminal word maps to the prefix before its rightmost \(2\), if there is one, and otherwise to \(R\). Every non-root chain therefore reaches \(R\), and there are exactly \(|W_m|\) parent edges on \(|W_m|+1\) vertices.

## 4. Fundamental cuts and the explicit canonical solution

For a terminal word \(w\), let \(v(w)\) be the prefix before its last zero when the suffix after that zero consists only of ones (the suffix may be empty). The component \(K_u\) of the address tree after removing \(e_u\), chosen not to contain \(R\), has boundary-row sum
\[
\Gamma_u=\sum_{z\in K_u}C_z=
\begin{cases}
B_u+B_{u0}+B_{u1},&|u|<m-1,\\
B_w,&|w|=m-1,\ v(w)\text{ undefined},\\
B_w+B_v+B_{v0}+B_{v1},&|w|=m-1,\ v=v(w).
\end{cases}\tag{4}
\]
The component descriptions are: for nonterminal \(u\), \(K_u=\{u\}\cup u2\{0,1,2\}^{\le m-|u|-2}\); for terminal \(w\) with no \(v(w)\), \(K_w=\{w\}\); for \(w=v0\,1^k\), \(K_w=\{w,v\}\cup v2\{0,1,2\}^{\le m-|v|-2}\). Only addresses of length at most \(m-1\) are included. Summing (1) over these components cancels internal address terms in pairs and gives (4).

Combining (2) and (4), the canonical solution (zero on non-pivot edges) is
\[
x_{e_u}(t)=
\begin{cases}
t_{m-|u|},&|u|<m-1,\\
t_1,&|u|=m-1,\ v(u)\text{ undefined},\\
t_1+t_{m-|v|},&|u|=m-1,\ v=v(u).
\end{cases}\tag{5}
\]
All sums are in \(\mathbb F_2\). Formula (5) is linear in \(t\), so it suffices to verify it on the \(m\) generation-basis right-hand sides to cover every one of the \(2^m\) masks at any fixed level.

## 5. Exact finite audit

The companion script audit_gf2_pivot_tree.py reconstructs the boundary rows and edge order from the repository module, performs (1), constructs the dual multigraph, and checks:
- every transformed column has at most two ones;
- (3) is a spanning tree and equals the lexicographic greedy spanning tree;
- its edges equal the packed solver's pivot columns;
- the least primal edge in each cut (4) is \(e_u\);
- (5) solves the original boundary system on all \(m\) generation-basis right-hand sides.

Independent scratch runs through level 10 reported exact agreement at every level. The audit checked 1, 2, ..., 10 basis right-hand sides respectively; by linearity this is all masks at each of those finite levels.

| level | vertices | primal edges | holes / pivots | nonzero dual edges | basis RHS |
|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 9 | 1 | 6 | 1 |
| 2 | 15 | 27 | 4 | 18 | 2 |
| 3 | 42 | 81 | 13 | 54 | 3 |
| 4 | 123 | 243 | 40 | 162 | 4 |
| 5 | 366 | 729 | 121 | 486 | 5 |
| 6 | 1,095 | 2,187 | 364 | 1,458 | 6 |
| 7 | 3,282 | 6,561 | 1,093 | 4,374 | 7 |
| 8 | 9,843 | 19,683 | 3,280 | 13,122 | 8 |
| 9 | 29,526 | 59,049 | 9,841 | 39,366 | 9 |
| 10 | 88,575 | 177,147 | 29,524 | 118,098 | 10 |

## 6. Precisely what remains

The remaining all-level geometric obligation is the **edge-order lemma**:

> For every level \(m\) and every address \(u\in W_m\), the least-indexed primal edge in the support of the cut vector \(\Gamma_u\) in (4) is exactly \(e_u\), the edge joining \(u\) to \(p_m(u)\) in the transformed dual multigraph.

Equivalently, the address tree (3) must be shown to be the lexicographically first dual spanning tree for every level. This is a geometric induction about the recursive Sierpiński vertex numbering and boundary-edge ordering. It is separated from the linear-algebra theorem and the tree-flow calculation.

Once this edge-order lemma is proved, Theorem 1 and (4) imply (5) at every level. The all-level H10 recurrence still additionally requires the separate local-moment and corner-gluing argument; it is **not** proved by this result.

## 7. Lean 4 proof decomposition

1. rowChangeInvertible: (1) preserves row space.
2. incidenceColumnsIndependentIffForest: the general \(\mathbb F_2\) incidence/forest lemma.
3. greedyPivotsAreSpanningTree: the lexicographic pivot theorem.
4. treeFlowSolution: derive (2) by summing over a tree component.
5. addressParentTree: prove (3) is a tree by decreasing-prefix chains.
6. fundamentalCutAddressFormula: prove the cancellation identity (4).
7. leastEdgeOfAddressCut: the remaining geometric edge-order induction.
8. canonicalGenerationSolution: derive (5), then return to the local H10 moment expansion.

The key advance is that the canonical GF(2) solve is reduced from opaque Gaussian elimination to an explicit address-tree flow. The finite computation and the remaining infinite-level proof obligation are kept separate.

## 8. Kernel formalization of the triangular row-change injectivity

Added PhiGenesis/H10/BoundaryRowTransform.lean. The module reuses the established telescoping identity for the complete ternary subtree and proves that equality of transformed rows at every address of a fixed level forces equality of the original rows at every such address.

The constructive inverse is the sum of transformed rows over the complete descendant subtree rooted at the address. This formalizes the injectivity part of the row-change obligation independently of the edge-order argument. It does not yet identify the least primal edge in a fundamental cut, nor does it prove that the resulting address-parent tree is the lexicographically greedy pivot tree. Those remain separate obligations.

This module uses exact address lengths and ZMod 2 arithmetic only. It makes no changes to the Python solver, its edge order, or the non-pivot-zero convention. Lean CI on the exact commit is required before marking the result kernel-verified.

## 9. Lean module visibility correction

The first CI attempt for the new injectivity module, commit `95ff1a8e7f6835227fecc6a4af0392153722c650`, failed while elaborating `PhiGenesis/H10/BoundaryRowTransform.lean`. The first errors were unknown identifiers `gasketBoundaryRowTransform` and `gasketAddressSubtreeRowSum`; the later implicit-variable and length errors were cascading consequences, not separate mathematical failures.

The cause was the Lean module visibility boundary: `IncidenceForest.lean` starts with `module`, so declarations are private by default unless explicitly exported. The row-transform definitions and their algebraic row-sum/cut theorems existed in that file but were not visible to an importing module.

The correction exports the two row-transform definitions with exposed bodies, and exports the subtree telescoping and two cut-row sum theorems. Their statements and proofs are unchanged. This is an API-visibility correction only; it does not alter the address parent map, the GF(2) equations, the canonical pivot convention, or the edge-order obligation.

The visibility correction is not counted as kernel-verified until the Lean workflow for the resulting exact commit completes `lake build PhiGenesis` successfully.

## 10. Export the coefficient-field dependency

The build for commit `985d81cd5f0c660a846ef4e92b0d238b4ae1e5bc` passed the setup/cache stage but failed while compiling `PhiGenesis/H10/IncidenceForest.lean` at target `3008/3016`. The exact diagnostics were `Unknown identifier ZMod` in the newly public row-transform declarations and their public theorem statements.

This is the second half of the module-boundary issue. Exporting the row-transform declarations in section 9 made the declarations visible to importers, but their coefficient type `ZMod 2` was still brought in by an ordinary (private) import. In a file beginning with `module`, dependencies used by public declarations must themselves be publicly imported. The correction is therefore to change the header to `public import Mathlib.Data.ZMod.Basic`. It changes import visibility only; no definitions, theorem statements, proof terms, or matrix conventions are changed.

The failed run was `41986819415` for the exact SHA above. The next exact-SHA Lean workflow must complete `lake build PhiGenesis` before these row-transform results are treated as kernel-verified.

## 11. Exact parent-component characterization for an internal address

The Lean theorem `gasketAddressParentIter_reaches_iff_twoSubtree` now proves both directions of the internal component description. For an internal address (u), an address (z) reaches (u) after finitely many applications of the parent map exactly when
[
z=uquad	ext{or}quad z=u2s
]
for some ternary suffix (s). The forward implication uses an exhaustive classification of incoming parent edges: an internal parent extension cannot point to the internal address (u), while a terminal parent edge preserves the displayed (u2)-prefix. The reverse implication uses the already-proved rank-decreasing path result for every address in the (u2)-subtree.

This identifies the address-tree component below the parent edge of every internal address, not merely its connectivity. It is the combinatorial premise needed to turn the internal cut-row sum formula into a sum over the actual tree component. It does not yet settle terminal parent-edge components, nor does it identify the abstract parent-tree edge with the least-indexed primal edge in the concrete Python edge order.

## 12. Export the address type and parent-iteration map

The Lean run `41988889016` for commit `df05adbddfeeca135e6ec668d7655fced556d911` failed in `IncidenceForest.lean` while elaborating the new public internal-component theorem. The diagnostics explicitly reported that `GasketAddress` and `gasketAddressParentIter` exist as private declarations but cannot occur in the type of a public theorem.

The fix exports the address subtype abbreviation and exposes the parent-iteration definition. This is necessary because the component theorem is intended as part of the module's public API, not as a private internal lemma. No address definition, parent rule, induction argument, or component statement is changed.

The new public theorem remains unverified until the next exact-SHA Lean build completes successfully.
