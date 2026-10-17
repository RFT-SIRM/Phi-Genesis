# Independent Verification and Test Boundaries

Phi-Genesis is a spectral-computation project and does not claim to perform seL4 kernel verification. This page documents the analogous evidence boundary: computational tests validate only the specified implementation, operator, configuration, and parameter range.

## What a test can support

- Reproduction of a finite numerical observation.
- Detection of implementation errors covered by the test.
- A documented negative result for the tested family and decision rule.

## What it cannot support by itself

- An all-level mathematical theorem.
- A physical mass-generation mechanism.
- An independent selection rule for \(\{1,12,17,40\}\).
- A claim about software or hardware systems not tested by the project.

For the actual computational methods and results, see [Verified Results](verified-results.md) and [Computational Architecture](computational-architecture.md).
