# Testing a spectral selection rule against the look-elsewhere effect: a worked negative example

Phi-Genesis v2.2.x. Short write-up of the method used in `PREREGISTRATION*.md` and `protocol_ledger.md`, and of what it found.

## 1. The question and the trap

The mass formula `m = A*n` matches four heavy-fermion masses with one scale `A` and integer indices `n` in {1, 12, 17, 40}. The question is whether a spectral rule on the Sierpinski gasket (SG) *selects* those indices, rather than the indices being chosen to fit.

The trap is the look-elsewhere effect. Every operator configuration yields a selected set of positions in the low spectrum; try enough configurations and some will match some of the targets. The repository's own history shows it: a Sierpinski-carpet search (about 128 configurations at level 3, plus a level-4 sweep) reported a "4/4" match, and a null test then showed that the four hits were statistically independent and that three or more of four hits occur by chance in roughly 11% of random trials. The hits are also not equally informative: under random on-site potentials the ratio-based selection rule picks index 1 about 95% of the time and index 40 about 3.4% of the time.

## 2. Design

- **Fixed before evaluation.** The selection rule (indices at the k largest ratios of consecutive nonzero eigenvalues, window of 60 positions), the targets, the statistic, the null ensembles, the pool sizes and the seeds are written down and committed first. Commit order for each protocol: rule and code, then null pools (Step A), then the evaluation (Step B), then the ledger. Results are committed as computed.
- **Null ensembles.** Generic operators of the same type: random oscillatory potentials and random edge weights on the gasket (v1.0, v1.1); a random circle radius and phase on the plain gasket, and the same with random potentials (v1.2.1). A configuration counts as a candidate only if the test reaches p <= 0.01 in both nulls.
- **Statistic.** Each target gets the weight -ln(base rate) estimated on one half of the null draws. A configuration scores the summed weights of the targets it selects. The test statistic is the best score over the M configurations of the family; its p-value comes from the null distribution of that maximum, estimated on the other half of the draws.
- **Power check before running.** From null draws alone, list which hit patterns could reach p <= 0.01. The first protocol failed this check when it was run afterwards: even a configuration selecting all four targets would have given p of about 0.14 to 0.22, so its "no evidence" carried no information. The later protocols chose k from null-only draws (k = 6 for v1.1, k = 8 for v1.2.1) so that the best possible outcome could reach the threshold.
- **Decoys.** Random 4-sets are scored the same way. If the targets do not stand out from random sets, a high score means little.
- **Ledger.** Every configuration ever tried is counted, including abandoned branches. When the carpet search turned out not to be recorded it was added and the cumulative numbers were restated as lower bounds. Where a new family is not independent of an earlier one (the continuum circle of v1.2.1 versus the lattice circle of F3), that is stated.
- **Labelling.** Analyses added after seeing results are marked post hoc.

## 3. Results

| Protocol | k | Configurations | p (null 1 / null 2) | Best configuration | Informative? |
|---|---|---|---|---|---|
| v1.0 | 12 | 75 | 0.922 / 0.968 | 3 of 4 targets | no (threshold unreachable) |
| v1.1 | 6 | 75 | 0.966 / 0.997 | 2 of 4; index 40 selected by none | yes |
| v1.2.1 | 8 | 10 | 0.953 / 0.926 | 1 of 4 (index 12) | yes |

Across the protocols, random 4-sets scored at least as high as the targets in 60% to 86.5% of draws. The ledger records 193 configuration evaluations since v1.0 plus the earlier carpet search, so at least about 321 in all.

## 4. What the negative does and does not say

It says that, for these operator families and this rule, no configuration selects the mass indices more often than chance allows, and that the two protocols able to reach the threshold did not. It does not say that no mechanism exists. The mass formula remains a numerical coincidence: four masses, one fitted scale, and four integers chosen with the masses in view. The top-quark index is unresolved (1654, 1664 or 1680 depending on how it is obtained).

## 5. Practical lessons

1. Fix the rule, the statistic and the nulls before looking at the family, and commit them.
2. Compute power from the null alone, before evaluation; an unreachable threshold makes a negative uninformative.
3. Weight hits by their null base rate; a hit on a near-universal index is not evidence.
4. Count everything, including abandoned branches and exploratory checks, and say when the count is a lower bound.
5. State dependence between families and label post hoc analyses.

## 6. Reproduce

```bash
pip install -e . pytest
python -m phi_genesis.selection_protocol_v121 stepA   # null pools (seeds fixed)
python -m phi_genesis.selection_protocol_v121 stepB   # compare with protocol_data/results_v1_2_1.json
```

Files: `PREREGISTRATION.md`, `PREREGISTRATION_v1.1_DRAFT.md`, `PREREGISTRATION_v1.2_DRAFT.md`, `PREREGISTRATION_v1.2.1.md`, `protocol_ledger.md`, `protocol_data/`, `phi_genesis/selection_protocol*.py`.
