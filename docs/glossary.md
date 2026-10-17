# Glossary

## Spectral decimation

A recursive relation connecting spectral data at successive graph approximations. In this project, the principal scaling factor is approximately five, with corrections for the corner-degree-2 Laplacian.

## Sierpiński gasket (SG)

The self-similar graph used as the main spectral substrate for the documented computations.

## Spectral dimension

The exponent associated with spectral counting. For the Sierpiński gasket, the theoretical value used here is \(d_s/2=\ln 3/\ln 5\approx0.6826\).

## Fukushima–Shima gaps

Forbidden spectral intervals associated with the spectral-decimation structure. The repository reports their finite-level numerical reproduction within the documented setup.

## Möbius / \(\pi\)-flux boundary condition

A boundary twist used to study how flux changes the graph spectrum. The tested full \(\pi\)-flux configuration opens a gap, but this does not establish the target mass-index rule.

## Target indices

The four integers \(\{1,12,17,40\}\) used in the proposed mass relation. Their independent derivation from a spectral invariant has not been established.

## Look-elsewhere effect

The statistical inflation of apparent significance when many configurations, rules, or parameter choices are tested. Phi-Genesis records configuration counts and preregistered decision thresholds to make this risk explicit.

## Null-only power check

A check, designed without looking at target outcomes, that establishes whether a protocol could reach its decision threshold under an idealized target-compatible result.

## Inertia count

The number of eigenvalues below a chosen threshold, computed from the inertia of a shifted matrix. The project's sparse-LU method is numerical and floating-point based, not a machine-checked proof.

## Evidence labels

- **Reproduced numerically:** observed again with documented computation and scope.
- **No evidence:** the tested protocol did not meet its predeclared threshold.
- **Not reproduced:** a prior claim was not obtained in the documented tests.
- **Open:** current evidence does not settle the question.
- **Fit, not prediction:** parameters or target indices were chosen using the data being matched.
