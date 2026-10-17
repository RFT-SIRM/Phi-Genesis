# Phi-Genesis Evidence Control Plane

Phi-Genesis keeps the status of its computational work visible and links summaries to the records needed to assess them. This page is a project-level evidence index, not a live CI monitor or a claim that every external workflow has passed.

## Research status

| Area | Current documented status | Authoritative record |
|---|---|---|
| Spectral decimation | Numerically reproduced within the stated scope, with corner-defect corrections | [Verified Results](verified-results.md) |
| Spectral exponent | Finite-window estimates remain sensitive to the estimator and window | [Open Problems](open-problems.md) |
| Target-index selection | Preregistered tests did not meet the threshold | [Selection Protocol](selection-protocol.md) |
| \(\eta\)-invariant value \(-4\) | Not reproduced in documented tests | [Verified Results](verified-results.md) |
| Reproducibility | Commands and source artifacts are documented | [Reproducibility](reproducibility.md) |

## Status meanings

- **Reproduced numerically:** obtained again with the documented computational setup and scope.
- **No evidence:** the specified test did not meet its predeclared decision threshold.
- **Not reproduced:** the documented tests did not recover a previous claim.
- **Open:** available evidence does not settle the question.
- **Fit, not prediction:** a parameter or target was fitted to data being matched.

## Evidence boundaries

A passing computational test does not by itself establish a general theorem. A numerical observation does not inherit the Lean verification status of the separate Evgeny-Theorem repository. The selection rule for \(\{1,12,17,40\}\) remains unestablished.

For versioned source records, see [README](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/README.md), [protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md), and [changelog](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/CHANGELOG.md).
