# Research log: uniform spectral gap at the central theta = 2 pi point

**Date:** 5 November 2026  
**Status:** an analytic lower-bound theorem is proved for the explicit recursive face/sign model below. Exact combinatorial and edge-gauge audits pass through level 10; low eigenvalues were computed numerically through level 8. The proposed limiting value near 1.30912892028081 is **not** proved.

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

For each ordered elementary upward face T=(a,b,c), the supplied convention flux={(f[0],f[1])} gives signed-adjacency signs:
- s_ab = +1 on the first edge;
- s_ac = s_bc = -1 on the other two edges.

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

1. The analytic lower bound is proved for the explicit recursive face/sign model specified above.
2. The supplied attachment did not contain the external sg.py source. The face order and sign convention were reconstructed from the pasted code and its six-vertex cell. The spectra reproduce the quoted values and the graph matches the repository's recursive Sierpinski graph, but exact source-to-source identity with the external faces(m) function still needs checking.
3. The exact limiting value near 1.30912892028081 remains an observation.
4. The supplied interior and boundary rational maps are not a global spectral-decimation theorem. Any further use must classify boundary data and exceptional modes.
5. No claim is made about general theta, noncentral SU(2) holonomies, Yang--Mills mass gaps, P vs NP, or continuum quantum field theory.
6. This separate workstream does not change the scalar canonical-signing H10 recurrence or its Lean obligations.

## 7. Next steps for the next session

1. Obtain the original sg.py and gap.py; compare ordered faces and edge signs exactly.
2. Formalize the triangle energy identity for Hilbert-valued vectors and the global lower-bound lemma in Lean.
3. Formalize recursive face decomposition, edge-disjointness, and vertex coverage for the exact Sierpinski address model.
4. After the lower-bound theorem is kernel-checked, study the sharper limit. Re-derive Schur elimination with both boundary and interior equations and classify eigenvalue branches before claiming a fixed point.
5. For 0 < theta < 2 pi, compute the local magnetic-triangle coercivity constant and check whether a face-wise estimate survives the chosen connection convention.

**Handoff:** the no-closing-gap question at theta = 2 pi has a clean analytic answer for the explicit model: a uniform lower bound of 1. The exact spectral edge and general-theta case remain open.
