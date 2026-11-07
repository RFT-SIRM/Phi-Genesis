# D₃ representation audit for Open Problem #1

**Status:** exploratory numerical diagnostic, reproduced on 7 November 2026. This is not a preregistered selection rule, a Lean theorem, or a proof that no spectral selection rule can exist.

## Scope and indexing

The calculation uses the same level-m Sierpiński-gasket graph and the unweighted corner-degree-2 combinatorial Laplacian constructed by `phi_genesis.sg_laplacian.sierpinski_graph`. The four target labels `{1, 12, 17, 40}` are **1-based positions in the positive spectrum**, as specified in `PREREGISTRATION.md`: the constant zero eigenvalue is removed first.

This convention matters. In the earlier exploratory D₃ script, the full spectrum was clustered from its first entry (the zero eigenvalue) while targets were read as `w[t - 1]`. That assigned the zero mode to target 1 and shifted every positive target by one. The table below corrects that off-by-one error.

## Method

At level m, represent a vertex by integer barycentric coordinates `(p,q,r)` with `p+q+r=2^m`. Permuting these three coordinates gives the six elements of `D₃ ≅ S₃`. The implementation verifies that each induced permutation is bijective and preserves the complete edge set.

For each numerically clustered eigenspace V_lambda, the code computes the six character traces of the restricted permutation action. The multiplicities of the irreducible representations are recovered from the character inner products:

- `A1`: the trivial one-dimensional representation;
- `A2`: the sign one-dimensional representation;
- `E`: the two-dimensional standard representation.

The low eigenspaces are computed with SciPy's dense symmetric subset eigensolver. This is intentional: an iterative sparse solver can return an incomplete basis from a highly degenerate eigenspace, which would make its character trace incorrect. Eigenvalue clusters are grouped numerically with absolute tolerance `1e-8`; the resulting classifications are computational, not exact-arithmetic certificates.

Reproduce from the repository root:

```bash
python -m phi_genesis.symmetry_probe
pytest -q test_symmetry_probe.py
```

## Corrected results

The complete cluster signature (cluster endpoints and A1, A2, E multiplicities) for the first 60 positive-spectrum positions is identical at levels 5, 6, and 7. The six D3 actions were verified as graph automorphisms at each of those levels.

| Target rank | Positive-spectrum cluster | Multiplicity | Representation | lambda, level 5 | lambda, level 6 | lambda, level 7 |
|---:|---:|---:|---|---:|---:|---:|
| 1 | 1–2 | 2 | E | 0.005741958474563 | 0.001154094053506 | 0.000231192288259 |
| 12 | 12–14 | 3 | A1 + E | 0.143567179457051 | 0.028880249655440 | 0.005782737942710 |
| 17 | 16–17 | 2 | E | 0.200112150540496 | 0.040496798530680 | 0.008122335554676 |
| 40 | 30–41 | 12 | 3A1 + A2 + 4E | 0.697224362268003 | 0.143567179457049 | 0.028880249655436 |

Here the last three columns give the eigenvalue of the full cluster containing the indicated target rank; all ranks in one cluster have that same eigenvalue within the stated numerical clustering tolerance.

The simple, fully symmetric (A1) eigenspaces in the first 60 positive-spectrum positions begin at

`3, 9, 18, 27, 48, 54`.

## Interpretation

Two different symmetry criteria should not be conflated:

1. **Contains an A1 component:** this criterion hits target ranks 12 and 40, because their complete eigenspaces contain A1. It does not hit 1 or 17. It selects whole degenerate eigenspaces (12–14 and 30–41), not the individual integer ranks.
2. **Is a simple, fully symmetric eigenspace:** none of the four target ranks meets this criterion. The list of simple A1 ranks above does not contain any of the four targets.

Thus the earlier claim that positive-spectrum ranks 12 and 17 are both pure E, while rank 1 is fully symmetric, was incorrect. The corrected result does **not** select `{1,12,17,40}`. It is a bounded negative result for these two natural D3 criteria only. It does not rule out every possible function of the spectrum, every operator family, or a future independently derived physical selection mechanism.

## Protocol v1.3 archive: pending source verification

A previous conversation summary reports a separate ancestry/decimation selection probe and gives selected-count and target-mask claims for levels 6 and 7. However, the ZIP archive and its source files/results are not present in the inspected repository or among the files available for this audit. Consequently those claims have **not** been independently rerun here, are not part of the verified table above, and are not added to the cumulative count of documented configuration evaluations.

To verify v1.3, the archive (or its complete source code, frozen inputs, and expected outputs) must be added to the repository. The check should reproduce the archived outputs from the specified graph, operator convention, positive-spectrum indexing, and tolerances before the result is promoted from pending to verified.

## Reopening condition

Reopen the finite selection search only when at least one of the following is supplied:

- the complete v1.3 archive and a reproducible independent check;
- a new operator family with an a-priori mathematical rationale, a frozen selection statistic, a null-only power analysis, and a preregistration made before target evaluation;
- a derivation of the target indices from an operator invariant that is independent of the masses used to identify the targets.

The four-mass fit remains a numerical fit, not a spectral prediction, until an independent rule is derived.
