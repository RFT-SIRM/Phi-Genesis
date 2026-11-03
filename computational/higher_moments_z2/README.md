# Reproducing the finite signed-Z2 H10 computations

Requires Python 3.10+, NumPy and SciPy.

```bash
python -m phi_genesis.higher_moments_z2 --validate-reference --max-level 10 --output /tmp/full_flux_h10.csv
pytest -q test_higher_moments_z2.py
```

The module computes the signed Laplacian using the project's deterministic GF(2) representative, exact sparse integer traces, and the identity Tr(L^10)=||L^5||_F^2. The reference solver and geometric boundary scan are checked through level 5.

## Evidence boundary

- Full-flux H10 traces are directly computed for levels 1--10.
- Complete generation-mask sweeps are supplied for levels 4--9.
- 1,008 transition checks across levels 3--9 pass.
- 156 level-10 masks are direct calculations and agree with the recurrence; other level-10 masks are predictions.
- The all-level recurrence is not proved or formalized in Lean 4.
- Hole parities do not determine the full cocycle; local representative choices affect H10.
- The scalar signed Z2 operator is distinct from the SU(2) operator in Evgeny-Theorem.

## Source files

- `phi_genesis/higher_moments_z2.py`: graph construction, packed GF(2) solver, signed Laplacian, exact trace routines, and Boolean correction.
- `test_higher_moments_z2.py`: finite regression tests.
