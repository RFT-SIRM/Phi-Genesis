# H10 all-level recurrence: mathematical checkpoint

**Date:** 4 November 2026  
**Model:** scalar signed Z₂-flux Laplacian on the recursive Sierpiński gasket.  
**Status:** the all-level recurrence is derived below by induction on the recursive geometry, together with an exact finite certificate for the exceptional transition \(3\to4\). It is **not yet a Lean-kernel proof**. This note supersedes the earlier pivot report's statement that the all-level edge-order lemma was still open.

## 1. Main theorem

Let
\[
F_m(t_1,\ldots,t_m)=\operatorname{Tr}(L_m(t)^{10}),
\]
where \(L_m=D_m-A_{s,m}\) uses the canonical GF(2) signing selected by the lexicographic pivot solver (all non-pivot edge variables are zero). Put \(a=t_1,\ b=t_2,\ c=t_3\). For every \(m\ge3\) and every Boolean generation mask,
\[
F_{m+1}(t_1,\ldots,t_m,d)=3F_m(t_1,\ldots,t_m)+Q(a,b,c,d),
\]
where
\[
\begin{aligned}
Q={}&127182024+89195520a+73945440b-145153920ab\\
&+55360c-150880ac+40320bc-39680abc\\
&+d(115347760-110022480a+10024960b\\
&\qquad-20854720ab+320c-640ac).
\end{aligned}
\]

For full flux, define
\[
D_m=F_m(1,\ldots,1)-F_m(0,\ldots,0).
\]
Since \(D_3=548852760\) and
\[
Q(1,1,1,1)-Q(0,0,0,0)=139569384-127182024=12387360,
\]
we obtain
\[
D_{m+1}=3D_m+12387360,\qquad
D_m=555046440\cdot3^{m-3}-6193680\quad(m\ge3).
\]
As \(|V_m|=(3^{m+1}+3)/2\),
\[
\lim_{m\to\infty}\frac{D_m}{|V_m|}=\frac{370030960}{27}.
\]

The arbitrary-mask closed form is
\[
F_m(t)=3^{m-3}F_3(a,b,c)+
\sum_{j=4}^{m}3^{m-j}Q(a,b,c,t_j).
\]

## 2. Why the GF(2) recursion is all-level

Index constraint rows by ternary addresses
\[
W_m=\bigcup_{j=0}^{m-1}\{0,1,2\}^j.
\]
Let \(B_u\) be the hole-boundary row and \(b_u=t_{m-|u|}\). Apply the invertible row change
\[
C_u=B_u+B_{u0}+B_{u1}+B_{u2}
\]
for internal addresses, and \(C_u=B_u\) for terminal addresses.

Geometrically, these rows are the boundaries of the recursively partitioned triangular regions: a central inverted triangle at an internal address and the terminal triangle at a leaf. Their interiors are disjoint, so every primal-edge column has weight 0, 1, or 2. The transformed matrix is therefore the incidence matrix over GF(2) of a dual multigraph with one extra exterior vertex \(R\).

For an internal \(u\), define
\[
p_m(u)=u0\,1^{m-|u|-2}.
\]
For a terminal \(w\), let \(p_m(w)\) be the prefix before its rightmost digit 2, or \(R\) if it has no 2. These parent relations form an address tree. The six corner/midpoint vertices of any cell have one of three recursive orders:

| State | Six vertices in increasing order |
|---|---|
| A | \(q_0,h_{01},h_{02},q_1,h_{12},q_2\) |
| B | \(q_0,q_1,h_{01},h_{02},h_{12},q_2\) |
| C | \(q_1,q_0,h_{01},h_{02},h_{12},q_2\) |

The root is A; child states are A/A/B from A and A/C/B from B or C. Hypotenuse vertices are monotone in first-occurrence order. These facts identify the least-indexed edge in every fundamental cut with the corresponding address-parent edge. Thus the address tree is the lexicographically first dual spanning tree. The standard incidence-matrix forest theorem then gives the canonical solution for every level: the value on a tree edge is the sum of transformed right-hand sides on the component away from \(R\), and all non-tree variables vanish.

The face-holonomy formula for generation \(j\ge2\) is
\[
S_{m,j}=\{u0\,1^{j-2}e:\ |u|=m-j,\ e\in\{0,1\}\}.
\]
Generation 1 is determined by the A/B/C state. This gives the child restriction law
\[
[\sigma_{m+1}|_0]=[\sigma_m]+d\Delta_m,\quad
[\sigma_{m+1}|_1]=[\sigma_m],\quad
[\sigma_{m+1}|_2]=[\sigma_m]+t_1\Delta_m,
\]
where
\[
\Delta_m=\{1^{m-1}0,1^{m-1}1\}.
\]

**Switching caveat:** these are switching-class identities, not always literal equality of raw edge masks. The two-edge \(\Delta_m\) representative is obtained by a vertex switching; traces and diagonal moments are unchanged by that conjugation. Exact switching checks cover every generation-basis direction and all three children through level 10.

## 3. Why Q is independent of higher generation bits

The mixed tenth-trace term for two children meeting at one vertex factors through diagonal moments at that vertex. Orders needed are at most 9, hence rooted radius 4 suffices. A generation-\(j\) odd upward face has address \(u0\,1^{j-2}e\); its distances from the three outer corners are bounded below by
\[
2^{j-1}-2,\qquad 2^{j-1},\qquad 2^j-1.
\]
For \(j\ge4\), these are at least 6, 8, and 15. The delta patch lies within distance 6 of its corner, so generations \(j\ge4\) are switching-trivial on all required local patches. Hole boundaries of such generations are too large to be contained in these patches.

The 15-vertex corner patch has cycle rank 13 = 9 upward faces + 4 contained small-hole boundaries. The 20-vertex two-edge delta patch has cycle rank 17 = 12 upward faces + 5 contained small-hole boundaries. Thus their cycle holonomies depend only on \(t_1,t_2,t_3\), plus the local delta bit. Exact integer patch calculations give
\[
R(a,b,c)=78396480-110751600a+4704800b-10553280ab+160c-320ac,
\]
with child corrections \(P_0=dR,\ P_1=0,\ P_2=aR\). The three pairwise junction terms add to \(Q\) above. This proves template stability for every child level \(m\ge4\).

The exceptional transition \(3\to4\) is checked for all 16 \((a,b,c,d)\) patterns by exact integer matrix traces. Together with the all-level argument for \(m\ge4\), this establishes the recurrence for all \(m\ge3\).

## 4. Exact audit and formalization boundary

Independent exact audits completed:

- dual column weights, parent-edge existence, spanning-tree property, and every fundamental-cut minimum through level 12;
- A/B/C corner order and side monotonicity for all 265,720 addressed cells at level 12;
- smallest-face holonomies for all 531,441 upward faces and all 12 generation basis vectors at level 12;
- switching-class child restriction checks through level 10;
- all 496 generation masks at levels 4–8, both values of the new bit: 2,976 pairwise junction checks, 496 delta-patch checks, and 992 Q checks, all with zero error;
- the exceptional transition \(3\to4\) for all 16 patterns;
- direct exact full-flux traces at levels 11 and 12.

Large traces use the symmetric-integer identity
\[
\operatorname{Tr}(L^{10})=\|L^5\|_F^2,
\]
with conservative int64 bounds below the signed limit.

**Not yet done:** Lean 4 formalization. The next step is to formalize the incidence/forest theorem, address-tree and cut lemmas, face-holonomy restriction, local finite matrices, and finally the all-level H10 theorem. Do not describe this result as Lean-kernel verified until that work is compiled and checked.

No README, website, or unrelated documentation is changed by this checkpoint.
