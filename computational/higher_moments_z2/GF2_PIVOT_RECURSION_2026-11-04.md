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

## 13. Export the parent-map symbol used by the public iterator

The Lean workflow `41989310255` for exact commit `2b40f9231c9d3aeaece509eac17424c30eadec1c` failed while compiling `PhiGenesis/H10/IncidenceForest.lean`. The first diagnostic was at line 1316: the exposed public definition `gasketAddressParentIter` referred to `gasketAddressParent`, which still had module-private visibility.

The iterator is intentionally exposed because its recursive equations are used by importing modules. Its defining body therefore must refer only to an exported parent-map symbol. The correction changes `gasketAddressParent` from a module-private definition to a public definition, without exposing the implementation of the parent map itself. This keeps the bounded-prefix helper and the rest of the implementation private while making the dependency name available to the exported iterator.

The later diagnostics in the same build (the recovery `sorry` terms, the two unsolved goals in the reachability proof, and the `change`/binder errors in the component theorem) followed the failed iterator declaration. They are not being counted as independently resolved; the next exact-SHA Lean build must determine whether any proof-level issue remains after the visibility dependency is fixed.

No parent rule, rank, address set, component characterization, theorem statement, or proof argument is changed. The update is an API-visibility correction only. The result remains unverified until `lake build PhiGenesis` succeeds on the new exact SHA.

## 15. Repair and consolidate the terminal-component formalization

The Lean workflow `41993578524` failed on the first terminal-component attempt, and the follow-up workflow `41995566102` exposed an additional repository-editing defect: the attempted insertion had duplicated the new theorem block and separated the existing forest doc-comment from its declaration. The second log also identified the successor-iteration proof and two subtype-equality transport errors in the terminal theorem.

The repair starts from the last green source state, commit `8a370e61b1e5ffb9c613f5b567294645975b976b`, and inserts the terminal block exactly once immediately before the existing forest doc-comment. The iterator successor proof generalizes the address variable before induction and uses congruence on the shared first parent step. The forward terminal-component proof is an explicit induction on the number of iterations. The reverse proof handles the terminal, its unique child, and descendants under v2 separately, transporting subtype equalities explicitly.

This clean reconstruction removes duplicate declarations and leaves the existing forest theorem and all previously green modules unchanged. The terminal-component result is not kernel-verified until the new exact-SHA `lake build PhiGenesis` succeeds.

## 16. Correct the parent-iterator successor law

The exact Lean run `41996212091` for commit `87f603ae61ff75871a0d7763f0501045ea7f2e5c` reached `lake build PhiGenesis` and failed at `IncidenceForest.lean:1513` in `gasketAddressParentIter_succ_eq_bind_parent`. The diagnostic showed that `funext` was being applied after `congr` had reduced the goal to an equality of options, not an equality of functions.

The proof is rewritten with an explicit `change` to expose both sides as `Option.bind` expressions. The induction hypothesis is then applied pointwise to the continuation function, and associativity of `Option.bind` completes the final equality. The iterator definition and the terminal-component theorem statement are unchanged.

The terminal-component result remains unverified until the next exact-SHA `lake build PhiGenesis` completes successfully.

## 17. Lean formalization of the A/B/C corner-order automaton

The exact green Lean baseline is commit `c64b317bf90092260346280c61dcf5b1735d86d2`, workflow `41996612258`. The next module, `PhiGenesis/H10/VertexOrder.lean`, encodes the three six-vertex orders from the H10 all-level checkpoint as finite lists and defines the child-state transition on address digits. It proves that every state order is a permutation of the six distinguished vertices, has no repetitions, ends at q2, and that the A/A/B versus A/C/B child table holds after every address prefix.

This is the finite automaton layer of the vertex-order proof. It does not yet prove that the symbolic six-vertex orders coincide with the first-occurrence IDs produced by the recursive graph constructor, nor does it prove hypotenuse monotonicity or the least-edge fundamental-cut lemma. Those remain the next geometric realization obligations. No Python code or solver ordering is modified.

## 18. Remove unused derived finite instances and prove the A/B/C table by cases

Lean workflow `41998579819` for `e861058597f83d375baec453173bb9474cec280d` failed in the newly added `VertexOrder.lean`. The full diagnostics identified two sources: deriving `Fintype` for the two small inductive enumerations triggered a generated `enumList`/membership instance mismatch, although no finite-type instance is required anywhere in this module; and the child-table proof used `rfl` before reducing the middle-child transition, whose value depends on whether the parent state is A or B/C.

The correction removes the unnecessary `Fintype` deriving from both enumerations, retaining `DecidableEq` and `Repr`. The child-table theorem now records the three append-transition equations separately, rewrites the conjunction with those equations, and then splits on the parent state so the middle-child branch simplifies explicitly. The state values, vertex orders, transition function, and theorem statements are unchanged.

This is a proof/elaboration correction only. The A/B/C module is not kernel-verified until the new exact SHA passes `lake build PhiGenesis`.

## 19. Remove the remaining unnecessary Fintype instance from corner vertices

The exact Lean run `42000284818` for commit `97888606801fc11dbbe4bea4e65fc65b233279ba` failed at `VertexOrder.lean:34`. Inspection of the complete source showed that the prior correction removed the derived `Fintype` instance from `GasketCornerOrderState`, but accidentally left the same deriving clause on `GasketCornerVertex`. That remaining generated `enumList` instance caused the identical membership coercion mismatch in the permutation proof.

The correction removes `Fintype` only from `GasketCornerVertex` as well. The module uses neither a finite-type enumeration nor a sum/product over this type; concrete list permutation and nodup facts remain decidable from the inductive constructors. The state and vertex constructors, orders, transition automaton, and theorem statements are unchanged.

This is the final remaining instance cleanup identified by that log. The module is not verified until the next exact-SHA `lake build PhiGenesis` passes.



## 20. Exact integer geometry of recursive child embeddings

The branch head before this block, `9164817a7417c67043d0aaf47776048ae00cd30b`, passed the full Lean build (workflow `42001194393`). The A/B/C module formalizes the abstract three-state order automaton, but its header leaves realization by the Python graph builder open.

The Python child map is `target + (point - old_corner)/2`. In triangular-lattice coordinates scaled by (2^n) at level (n), the three child maps from level (n) to (n+1) become exact integer translations ((x,y)), ((x+2^n,y)), and ((x,y+2^n)). The new `PhiGenesis/H10/GasketCoordinates.lean` formalizes these maps without floating point or rounding. It proves injectivity of each child embedding, preservation of the parent triangle, the three pairwise-intersection constraints, and attainment of the shared midpoints by child outer corners.

An independent arithmetic sandbox check of this coordinate recursion gave the expected vertex counts ((3^{n+1}+3)/2) for levels 0 through 8 and verified the three singleton pairwise intersections at each positive level.

This is only the exact geometric gluing foundation. It does not yet prove the A/B/C first-occurrence state transitions from the ordered vertex list, side monotonicity, or the minimum-edge fundamental-cut lemma. The module is not kernel-verified until the exact-SHA Lean workflow completes `lake build PhiGenesis`.



## 21. Kernel model of the first-occurrence vertex enumeration

The previous green commit `c6e527d6953f25094e781c66ca3c97ba48181638` passed `lake build PhiGenesis` (workflow `42002762609`, 3018 successful jobs). The exact child embeddings are now in integer triangular-lattice coordinates.

The new module `PhiGenesis/H10/GasketVertexOrder.lean` formalizes the vertex-ID assignment rule from `sierpinski_graph_with_holes`: concatenate the three child vertex lists in order 0, 1, 2, map each through its exact integer embedding, and retain the first occurrence of each point. It proves:
- the first-occurrence scan preserves exactly the input membership set;
- the resulting list is duplicate-free;
- the recursively generated level-n vertex list is duplicate-free for every n;
- each of the three parent outer corners remains present in the next recursively generated list.

This is the first Lean definition of the actual recursive vertex discovery order, rather than a standalone A/B/C automaton. The module deliberately does not yet assert that the A/B/C six-vertex table follows: that requires deriving the six local corner/midpoint positions from this global first-occurrence list and proving the side-order monotonicity. The least-indexed primal-edge/fundamental-cut theorem remains open.

The module is not considered kernel-verified until the exact SHA passes the complete `lake build PhiGenesis`.



## 22. Repair Boolean-filter proofs in the first-occurrence scan

The exact Lean run `42003790338` for commit `a41e0da6862948f115408a570fe3993f93b0ebb1` failed in `GasketVertexOrder.lean`. The full log identified the primary issues: one induction hypothesis was applied without its list argument; the completeness proof tried to use proposition-level `¬ a = b` where `List.filter` requires the Boolean equation `decide (a ≠ b) = true`; the filter-length bound was left as an unapplied theorem; and the nodup proof attempted to use `rfl` as a proof of a Boolean filter equation.

The correction makes the induction-hypothesis list argument explicit, closes the empty-list cases from their impossible membership hypotheses, converts inequality to the exact Boolean predicate equation, applies `List.length_filter_le` with both arguments, and derives a contradiction from the filtered membership of the head. The recursion, first-occurrence order, generated vertex list, and theorem statements are unchanged.

This correction is proof/elaboration-only. The recursive vertex-order module is not considered kernel-verified until the next exact-SHA `lake build PhiGenesis` succeeds.



## 23. Correct the first-occurrence completeness proof from the full CI diagnostics

Lean workflow `42004260138` for exact commit `58f64826a5b0fef653007fa6571f0ad5fc4fc761` failed again in `GasketVertexOrder.lean`. The full job log confirmed that the previous revision had not actually changed the two empty-list branches or the filter-membership block. The unresolved diagnostics were: impossible membership in an empty list was not eliminated through its hypothesis; proposition inequality was supplied where the Boolean filter requires `decide (a ≠ b) = true`; and `List.length_filter_le` was left unapplied.

This revision changes both empty-list branches to simplify the impossible membership hypothesis `ha`, supplies the Boolean inequality equation explicitly, and applies `List.length_filter_le` to the explicit Boolean predicate and list. The recursive first-occurrence definition and all vertex-order statements remain unchanged. The nodup argument continues to derive contradiction from filtered membership of the head.

This is still an unverified proof repair until the exact new commit passes the full `lake build PhiGenesis`.



## 24. Avoid predicate over-normalization in the first-occurrence completeness proof

Lean run `42004872852` for `fa5ddf5fc24e6734ade9f80da003e9073e6bf802` reduced the remaining failure to one goal at `GasketVertexOrder.lean:81`. The induction hypothesis already proves membership in the filtered tail, but the final broad `simp` normalized the Boolean filter predicate `decide (x ≠ b)` to `! decide (x = b)`, so it no longer matched the hypothesis syntactically.

The correction does not unfold or normalize the filter predicate. It changes the goal directly to the constructor form of the recursive first-occurrence scan and closes the second disjunct with the existing induction-hypothesis result. The recurrence, theorem statements, and mathematical content are unchanged.

This is a targeted elaboration repair. The module remains unverified until the exact next SHA passes the full Lean build.



## 25. Unfold the recursive scan before applying the membership induction hypothesis

The exact run `42005758239` for commit `aaff8016f5a8073ce535daa53d4703eb44a40253` reduced the entire remaining module failure to one failed `change` at the completeness theorem. The target was still expressed as membership in `gasketFirstOccurrencesAux (fuel + 1) (b :: bs)`; it was not definitionally presented as the required disjunction because the recursive definition had not been unfolded.

The correction explicitly simplifies only with `gasketFirstOccurrencesAux` and `List.mem_cons`, then closes the second disjunct with the already established induction hypothesis `hrec`. This avoids broad simplification of the Boolean filter predicate and uses the same `simp only [gasketFirstOccurrencesAux, List.mem_cons]` pattern already used successfully in the membership lemma above.

This is the final single diagnostic reported by the preceding run. The module is not considered closed until the exact new SHA passes `lake build PhiGenesis`.
