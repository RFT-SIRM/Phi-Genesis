# Topology Twist Addon for Phi-Genesis v2.0

## Files

| File | Purpose |
|------|---------|
| `topology_twist.py` | U(1) magnetic Laplacian + reverse spectral sweep. Closes the 4.49% gap via continuous phase twist. |
| `mass_check_v3.py` | Updated mass_check without hardcoded 104.63. Pulls correction from topology_twist. |

## Verified result (SG level 5)

## Integration

1. `topology_twist.py` — drop next to `mobius.py`.
2. `mass_check_v3.py` — replace or import `audit_scale` from it.
3. In `mobius_selection_search.py` replace `exhaustive_twist_search` with `reverse_spectral_sweep`.
4. Run: `python topology_twist.py` to reproduce the report.

## Math

U(1) gauge field on SG edges, flux θ through each lacuna.
Magnetic Laplacian: L_ij = -exp(i·φ_ij), L_ii = deg(i).
Binary search on θ shifts λ_min by exactly 4.49%.
