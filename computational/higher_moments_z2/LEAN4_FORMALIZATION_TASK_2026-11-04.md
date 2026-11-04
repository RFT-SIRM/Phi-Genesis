# Phi-Genesis H10 — Lean 4 formalization task

**Prepared:** 4 November 2026  
**Target repository:** RFT-SIRM/Phi-Genesis  
**Baseline main commit:** 5fd373ebadd0fcfd7e94e835197a2aa428fa70a1  
**Purpose:** a durable handoff for the next implementation session. This is a proof task, not a documentation/PR task.

## 0. Current repository state — read first

- The scalar signed-Z₂ H10 research module is **phi_genesis/higher_moments_z2.py**.
- The mathematical checkpoint is **computational/higher_moments_z2/H10_ALL_LEVEL_CHECKPOINT_2026-11-04.md**.
- The detailed proof route and audit bundle are in the local handoff file **H10_ALL_LEVEL_RECURSION_2026-11-04.md** and **phi_genesis_h10_all_level_audit_bundle_2026-11-04.zip**.
- The previous pivot note is **computational/higher_moments_z2/GF2_PIVOT_RECURSION_2026-11-04.md**.
- There are currently **no .lean files, no lakefile.lean, and no lean-toolchain** in this repository. A Lean project must be created from scratch.
- The current working container has no lean or lake executable. Do not claim local Lean compilation. Build and verify through a pinned Lean/Mathlib setup and GitHub Actions.
- The Mathlib master toolchain checked on 4 November 2026 is **leanprover/lean4:v4.36.0-rc2**. Pin a compatible Mathlib revision rather than following a moving branch in a reproducible proof run.
- Current main HEAD is **5fd373ebadd0fcfd7e94e835197a2aa428fa70a1**. The immediately preceding commits **0b761cb** and **5fd373e** add and then correct the H10 checkpoint only. **README, website, and phi_genesis/higher_moments_z2.py have not been changed by these checkpoint commits.**
- The repository's scalar signed-Z₂ Laplacian is a different mathematical object from the SU(2) operator in Evgeny-Theorem. Do not mix their definitions or claim that one theorem automatically proves the other.

## 1. Mathematical target

For level m, let F_m(t₁,…,tₘ) = Tr(L_m(t)¹⁰) for the exact canonical signing selected by the existing GF(2) solver (all non-pivot edge variables are zero). The intended theorem is

\[
F_{m+1}(t_1,\ldots,t_m,d)
=3F_m(t_1,\ldots,t_m)+Q(t_1,t_2,t_3,d),\qquad m\ge3,
\]

for every Boolean generation mask, with

\[
\begin{aligned}
Q(a,b,c,d)={}&127182024+89195520a+73945440b-145153920ab\\
&+55360c-150880ac+40320bc-39680abc\\
&+d(115347760-110022480a+10024960b\\
&\qquad-20854720ab+320c-640ac).
\end{aligned}
\]

For full flux, define D_m = F_m(1,…,1)-F_m(0,…,0). The target consequence is

\[
D_{m+1}=3D_m+12387360,\qquad
D_m=555046440\cdot3^{m-3}-6193680\quad(m\ge3),
\]

and, using |V_m|=(3^{m+1}+3)/2,

\[
\lim_{m\to\infty}\frac{D_m}{|V_m|}=\frac{370030960}{27}.
\]

The theorem is specifically about the repository's deterministic canonical representative. It is **not** a theorem that 12,387,360 is invariant under all signings with the same hole-boundary parities. The genuine switching invariant is the full signed-graph switching class / complete cycle-holonomy data.

## 2. Non-negotiable proof discipline

1. No sorry, admit, new axioms, unsafe proof shortcuts, or unverified external certificates in the final theorem.
2. Keep a strict distinction between:
   - a paper proof / mathematical derivation;
   - a finite exact computation;
   - a theorem checked by Lean's kernel.
3. Every finite matrix certificate must be specified by explicit integer entries and checked in Lean by norm_num, decide, native_decide only where acceptable, or a transparent executable certificate verified by a theorem. Do not merely import CSV values as trusted facts.
4. Use exact combinatorial vertex/edge/address definitions. Do not use floating-point coordinates in Lean.
5. Preserve the existing Python solver as a reference implementation. Do not change the canonical edge ordering or the rule "non-pivot variables = 0" while formalizing.
6. Do not work on README, MkDocs, HTML, visualisations, or publicity copy during this task.
7. Before proving the final recurrence, reconcile every proof-note formula with the actual Python implementation and finite audit scripts.

## 3. Phase 0 — mathematical audit before Lean code

This phase is mandatory; it protects us from formalizing an incorrect derivation.

### 3.1 Freeze the exact combinatorial model

Reconstruct, from higher_moments_z2.py, the recursive vertex order, edge order, hole boundary rows, generation right-hand sides, and canonical GF(2) solution. Give each definition a precise Lean counterpart and verify that its finite enumerations agree with the Python source at small levels.

### 3.2 Recheck the proof route

Audit each statement in H10_ALL_LEVEL_CHECKPOINT_2026-11-04.md and the detailed proof note:

- triangular row change B ↦ C is invertible and really preserves the specified pivot columns;
- transformed boundary matrix has exactly 0, 1, or 2 ones in every edge column;
- the dual multigraph is connected, with parallel edges handled correctly;
- the address-parent relation defines a tree and the described K_u are exactly the components after deleting parent edges;
- the cut vectors are computed using the correct sorted primal-edge order;
- the A/B/C six-vertex state table follows from the actual first-occurrence concatenation, not only from finite examples;
- the minimum-edge/cut argument also covers the terminal v(w) case;
- the face-holonomy basis is complete and has the stated rank;
- child restrictions are stated up to vertex switching unless literal equality has independently been proved;
- the three-copy decomposition and cyclic word coefficient 10/r count every ordered trace word exactly once;
- rooted radius-4 corner moments and the two-edge defect patch contain every walk that can affect the tenth trace;
- full vertex degrees are retained on local-patch diagonals;
- the exceptional 3 → 4 transition is exact for all 16 Boolean patterns.

### 3.3 Resolve equivalent Boolean polynomial forms explicitly

The older FOLLOWUP_2026-11-03.md writes

\[
P_2=a(-32355120-5848480b-160c),
\]

whereas the later checkpoint writes P₂=aR(a,b,c), with

\[
R(a,b,c)=78396480-110751600a+4704800b-10553280ab+160c-320ac.
\]

These are equal on Boolean inputs because a²=a. The Lean file must encode and prove this normalization lemma rather than silently treating the two expressions as identical polynomials over ℤ without the Boolean hypothesis.

### 3.4 Make the audit suite reproducible

The bundled RUN_ALL_AUDITS.sh did not complete under the current container's 120-second limit: the pivot run reached level 11 before timing out; on a separate attempt the face-holonomy sweep reached level 8 before the overall command timed out. The canonical-solution and A/B/C vertex-order scripts completed through level 12. Do not state that the entire bundle completed in one run.

Split the audit suite into independently invocable, time-bounded jobs; cache graph/address data; report per-level completion and exact counts. Make CI fail on timeout/nonzero exit, not just on job creation. Verify the stored CSVs against their generating scripts.

**Phase 0 exit condition:** a reviewed proof-obligation table marks each statement as proved on paper, finite-checked, or still open. No main recurrence theorem is introduced until this table is internally consistent.

## 4. Phase 1 — create a reproducible Lean project

Create a minimal Lake project with:

- a pinned lean-toolchain;
- a pinned Mathlib dependency compatible with that toolchain;
- lakefile.lean with one library target;
- CI that runs lake build on every relevant commit;
- a small smoke-test module importing the required matrix, finite graph, F₂/ZMod 2, and list/finset APIs.

Do this first and make the empty project build green before writing the mathematical modules. Avoid adding a huge, moving dependency surface.

## 5. Phase 2 — GF(2) incidence and the canonical pivot solution

Suggested modules:

- PhiGenesis/H10/Addresses.lean
- PhiGenesis/H10/GasketGraph.lean
- PhiGenesis/H10/BoundarySystem.lean
- PhiGenesis/H10/DualTree.lean
- PhiGenesis/H10/CanonicalCocycle.lean

Required declarations (names indicative, choose Mathlib-consistent names):

1. addressChildren and the finite address set W m.
2. boundaryRow and the transformed row transformedBoundaryRow.
3. rowChange_involutive_or_inverse: prove the triangular row change is invertible.
4. transformedColumnWeight_le_two.
5. Define the dual multigraph with an exterior vertex R; retain parallel edges and discard zero columns.
6. incidence_columns_independent_iff_forest over ZMod 2.
7. greedy_pivots_eq_lexicographic_spanning_tree.
8. addressParentTree and the exact component formula for each K_u.
9. fundamentalCutRowSum.
10. leastEdge_internalCut and leastEdge_terminalCut, proved from the recursive vertex order and A/B/C state.
11. canonicalGenerationSolution: the closed form for the existing solver's canonical solution, with all non-pivot variables zero.

Do not conflate "independent columns scanned left-to-right" with an arbitrary Gaussian-elimination implementation. Prove that the exact solver convention in Python has the same pivot set as the dual-graph greedy tree.

## 6. Phase 3 — A/B/C order automaton and face holonomy

Modules:

- PhiGenesis/H10/VertexOrder.lean
- PhiGenesis/H10/FaceHolonomy.lean

Prove by induction:

1. the three-block first-occurrence vertex order;
2. strict monotonicity along every addressed hypotenuse;
3. the six-vertex A/B/C classification;
4. the transition table A ↦ (A,A,B), B ↦ (A,C,B), C ↦ (A,C,B);
5. the formula for odd upward-face sets S_{m,j} for j ≥ 2;
6. the formula for S_{m,1} and the Δ_m recursion;
7. completeness of the cycle basis (upward faces plus hole boundaries);
8. the restriction of the canonical cocycle to each child, as a switching-class equality.

Prove vertex switching as conjugation L' = SLS and derive invariance of all traces and diagonal moments used below. Use this to handle the child restriction cleanly.

## 7. Phase 4 — exact tenth-trace gluing

Module:

- PhiGenesis/H10/TraceGluing.lean

Prove:

1. L_parent = A₀ + A₁ + A₂ for the three embedded child Laplacians.
2. no ordered length-10 word involving all three child labels can contribute for child level m ≥ 2.
3. the two-child mixed contribution factors through diagonal moments at the shared junction.
4. the cyclic word count gives the exact coefficient 10/r.
5. the full trace decomposition into the three child traces and G₀₁+G₀₂+G₁₂.

The ordered-word expansion must preserve factor order and multiplicity; do not quotient words by cyclic rotations before proving the trace identity.

## 8. Phase 5 — finite local certificates and Q

Modules:

- PhiGenesis/H10/LocalPatches.lean
- PhiGenesis/H10/CorrectionPolynomial.lean

Encode the finite integer data for:

- the 15-vertex radius-4 corner patch, with the original full degrees on the diagonal;
- the 20-vertex two-edge defect patch, also with full degrees on the diagonal;
- the 9 diagonal moments required per junction;
- the eight Boolean values of R(a,b,c);
- the 16 Boolean values of G₀₁,G₀₂,G₁₂,Q.

Prove the patch moment identities exactly. Prefer a transparent finite computation checked by Lean's kernel over pasted decimal results. Add the Boolean normalization lemma a²=a and verify P₀=dR, P₁=0, P₂=aR on Boolean inputs.

Prove that generations j ≥ 4 have trivial switching class on the needed rooted patches, using the address/hole-distance bounds. This is the point that makes the local Q templates level-independent.

## 9. Phase 6 — base transition, recurrence, closed form

Modules:

- PhiGenesis/H10/Recurrence.lean
- PhiGenesis/H10/Asymptotic.lean

Prove the finite m=3 → 4 bridge exactly for all 16 Boolean patterns. Then combine the all-level child restriction, trace gluing, and finite local certificates to prove

\[
F_{m+1}(t_1,\ldots,t_m,d)=3F_m(t_1,\ldots,t_m)+Q(t_1,t_2,t_3,d)
\]

for every m ≥ 3. Derive the arbitrary-mask closed form, full-flux affine recurrence, closed formula, and normalized limit by induction and exact algebra.

## 10. CI and completion criteria

The formalization is complete only when all of the following hold:

- lake build succeeds from a clean checkout using the pinned toolchain and pinned Mathlib dependency;
- no sorry, admit, new axioms, or unsafe proof shortcuts occur in the theorem dependency graph;
- all finite certificates are checked by Lean, not trusted from Python output;
- the all-level recurrence theorem has no transport/locality hypotheses left as assumptions;
- full-flux closed form and normalized limit are theorems derived from the recurrence;
- Python audit scripts and Lean finite certificates agree on base cases and all recorded test levels;
- the proof note lists exact theorem names and the commit at which the Lean build passed.

A passing Python audit is evidence, not a substitute for the Lean theorem. A paper proof is evidence, not a kernel check.

## 11. First work session

The next session should do only this:

1. read this task and both H10 proof notes;
2. reproduce the light audits (canonical solution, vertex order, small face-holonomy cases, Boolean Q truth table);
3. create the pinned Lake/Mathlib scaffold on this branch;
4. get the empty Lean project building in CI;
5. implement only the generic ZMod 2 incidence/forest theorem and its tests.

Do not start by formalizing the enormous trace expression. Establish the generic incidence theorem first, then grow the dependency chain one verified layer at a time.

## 12. Explicit stop conditions

Stop and report a mathematical discrepancy instead of patching around it if:

- the exact Python pivot set differs from the dual-tree minimum spanning tree;
- any address/cut formula fails on an exhaustively checked small level;
- the A/B/C transition depends on more than the stated three-state information;
- a high-generation face intersects a claimed local patch;
- any of the 16 Q values or any full trace differs;
- a local matrix omits an external degree contribution on its diagonal.

No README, website, marketing text, or Mathlib PR is part of this task.
