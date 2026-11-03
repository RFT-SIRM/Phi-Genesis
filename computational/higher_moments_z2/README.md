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


## Follow-up structural audit (3 November 2026)

- Detailed finite audit: FOLLOWUP_2026-11-03.md
- Full-flux exact traces: full_flux_h10_levels_1_10.csv
- Correction truth table: Q_truth_table_16.csv
- Alternative local-perturbation residuals: edge2_alternative_residuals_transitions_4_7.csv

The follow-up includes 1,016 directly computed generation-mask traces at levels 3–9, 1,008 exact transition checks, and a three-copy decomposition checked on 112 masks at parent levels 4–6. The all-level recurrence remains unproved and is not formalized in Lean 4.
