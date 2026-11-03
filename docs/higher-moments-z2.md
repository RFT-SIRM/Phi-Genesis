# Higher moments for the signed Z2-flux Laplacian

**Evidence status:** exact finite-level integer computations. The observed recurrence is not an all-level theorem and has not been formalized in Lean 4.

This is a separate scalar signed-graph experiment from the noncommutative SU(2) trace-defect results in [Evgeny-Theorem](https://github.com/RFT-SIRM/Evgeny-Theorem).

## Operator and representative

At level m, let
$$
L_m=D_m-A_{s,m},
$$
where D is the ordinary degree matrix and A_s is the signed adjacency matrix. The GF(2) system prescribes one parity equation for each listed hole boundary. The solver sets non-pivot edge variables to zero. Thus every numerical statement below concerns this deterministic representative, not every cocycle satisfying the same hole parities.

For a generation mask t, bit i-1 specifies whether holes of generation i have odd (1) or even (0) boundary parity.

## Full-flux tenth trace

Define
$$
D_m^{(10)}=\mathrm{Tr}(L_{\pi,m}^{10})-\mathrm{Tr}(L_{0,m}^{10}).
$$

| m | Vertices | Edges | Holes | D_m^(10) | D_m^(10)-3D_(m-1)^(10) |
|---:|---:|---:|---:|---:|---:|
| 1 | 6 | 9 | 1 | 19,523,880 | — |
| 2 | 15 | 27 | 4 | 178,774,440 | 120,202,800 |
| 3 | 42 | 81 | 13 | 548,852,760 | 12,529,440 |
| 4 | 123 | 243 | 40 | 1,658,945,640 | 12,387,360 |
| 5 | 366 | 729 | 121 | 4,989,224,280 | 12,387,360 |
| 6 | 1,095 | 2,187 | 364 | 14,980,060,200 | 12,387,360 |
| 7 | 3,282 | 6,561 | 1,093 | 44,952,567,960 | 12,387,360 |
| 8 | 9,843 | 19,683 | 3,280 | 134,870,091,240 | 12,387,360 |
| 9 | 29,526 | 59,049 | 9,841 | 404,622,661,080 | 12,387,360 |
| 10 | 88,575 | 177,147 | 29,524 | 1,213,880,370,600 | 12,387,360 |

The data satisfy
$$
D_m^{(10)}=3D_{m-1}^{(10)}+12,387,360
$$
for the checked transitions m=4,...,10 only. This is finite evidence, not a theorem for every m.

## Generation-twist recurrence

Let
$$
F_m(t_1,\ldots,t_m)=\mathrm{Tr}(L_m(t_1,\ldots,t_m)^{10}).
$$

Complete exact sweeps were computed for every mask at levels 4--9 (16, 32, 64, 128, 256, and 512 masks). All 1,008 transitions from level 3 to level 9 satisfy a common correction polynomial:
$$
F_{m+1}=3F_m+Q(t_1,t_2,t_3,t_{m+1}).
$$
With a=t1, b=t2, c=t3, d=t_(m+1),
$$
\begin{aligned}
Q(a,b,c,d)={}&127182024+89195520a+73945440b-145153920ab\\
&+55360c-150880ac+40320bc-39680abc\\
&+d(115347760-110022480a+10024960b\\
&\qquad-20854720ab+320c-640ac).
\end{aligned}
$$
The exceptional 2-to-3 transition has a different correction; see the source module and CSV truth table. At level 10, 156 masks were directly evaluated and all agree with the later recurrence. Other level-10 mask values are predictions, not direct matrix-power calculations. The complete Boolean sweeps are injective: all trace values within each level 4--9 sweep are distinct.

## Why this is not a hole-flux invariant

Hole-boundary parities do not uniquely determine all elementary-triangle holonomies. At level 5 the graph cycle-space rank is 364, while the 121 hole-boundary constraints have rank 121. The audited elementary-triangle patterns retain 243 degrees of freedom. Moving the negative local triangle within one of the four-triangle groups preserves all prescribed hole parities but changes the tenth trace. Therefore the H10 value belongs to the chosen cocycle representative, not to hole flux alone.

## Exact arithmetic and validation

For symmetric real L,
$$
\mathrm{Tr}(L^{10})=\|L^5\|_F^2.
$$
The implementation uses integer sparse arithmetic and checks a conservative int64 bound. The optimized boundary walk and packed GF(2) solver are compared with the original geometric boundary scan and dense RREF solver through level 5, including all generation masks at those levels. The regression tests also compare Frobenius and sequential sparse-power traces.

## Follow-up structural audit — 3 November 2026

The follow-up extended direct generation-mask calculations to every mask at levels 3–9: 1,016 exact traces and 1,008 transition checks. Every checked transition agrees with one correction polynomial \(Q(t_1,t_2,t_3,t_{m+1})\).

A separate three-copy audit checked all 112 masks at parent levels 4–6. It decomposes the correction as \(Q=P+G\): local child-restriction changes give \(P\), while the three pairwise junction-word sums give \(G\). The corner-moment audit contains 336 observations and 48 stable signatures.

At level 5, 243 individual edge flips preserve the prescribed hole parities, yet every one changes H10. Thus 12,387,360 belongs to the chosen deterministic representative family, not to hole flux alone. The exact switching invariant belongs to the full signed-graph switching class.

These remain finite structural checks, not an all-level theorem or a Lean 4 formalization. See the [follow-up note](../computational/higher_moments_z2/FOLLOWUP_2026-11-03.md), [full-flux table](../computational/higher_moments_z2/full_flux_h10_levels_1_10.csv), [Q truth table](../computational/higher_moments_z2/Q_truth_table_16.csv), and [local perturbation audit](../computational/higher_moments_z2/edge2_alternative_residuals_transitions_4_7.csv).

## Relation to SU(2) H10

The central lift identity
$$
\mathrm{Tr}((L\otimes I_2)^{10})=2\mathrm{Tr}(L^{10})
$$
is valid for this scalar L. It does not identify the scalar Z2-flux defect with the SU(2) axis-orientation defect. These are different operators and proof obligations; their coefficients must not be interchanged.

## Open proof target

Prove the copy-restriction and corner-moment identities at every level, derive Q from the three-copy word expansion, and formalize the recurrence in Lean 4. Until then, the recurrence and any normalized limit derived from it remain finite computational evidence or conditional consequences only.

See [the implementation](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/phi_genesis/higher_moments_z2.py), [reproduction instructions](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/computational/higher_moments_z2/README.md), and [the repository README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md).
