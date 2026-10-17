# Selection Protocol and Search Audit

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


## Research question

Does any tested operator family on Sierpiński-gasket graph approximations select the target indices \(T=\{1,12,17,40\}\) more often than expected by chance, after accounting for the number of configurations tried?

The target indices were identified from a mass fit; therefore a match is not independent evidence by itself. The selection search uses a look-elsewhere correction over the configurations within each family, null ensembles, target weights based on null base rates, and a predeclared decision threshold of \(p\le0.01\) in **both** null ensembles.

## Preregistered results

| Protocol | Family / rule | Configurations | Result | Power status |
|---|---|---:|---|---|
| v1.0 | F1 + F2 + F3; \(k=12\), window 60 | 75 | No evidence; p = 0.922 / 0.968 | Threshold unreachable; negative is uninformative about whether the family contains a rule. |
| v1.1 | Same family; \(k=6\), window 60 | 75 | No evidence; p = 0.966 / 0.997 | Threshold reachable; informative negative for these configurations. |
| v1.2.1 | SG × S¹ continuum circle, two spin structures; \(k=8\), window 60 | 10 | No evidence; p = 0.953 / 0.926 | Threshold reachable; informative negative for these configurations. |

The p-value pairs are ordered as documented in the source records (N-pot / N-edge for v1.0 and v1.1; N-circ / N-circpot for v1.2.1). Each pair fails the requirement that **both** nulls meet the threshold.

The cumulative ledger records 193 configuration evaluations from the documented main families, plus an earlier Sierpiński-carpet search of about 128 level-3 configurations and an unrecorded level-4 sweep. The honest cumulative statement is therefore **at least about 321**, not an exact exhaustive count.

## Other relevant checks

- **Generation twists:** all 32 \(2^5\) configurations at level 5 were tested; maximum target overlap was 1 of 4, and index 40 was never selected.
- **Base-rate audit:** under random on-site potentials, the ratio-based rule selected index 1 about 95% of the time, while index 40 appeared about 3.4% of the time. Hits on the four indices are therefore not equally informative.
- **Carpet branch:** the early 4/4 match was reassessed against a null model; the record attributes it to a look-elsewhere effect and marks that branch abandoned.
- **v1.0 power correction:** even a configuration selecting all four targets would not have reached the required p-value. This was documented as a limitation of that protocol rather than treated as evidence against all possible mechanisms.

## What the result means

The tested families did not satisfy the preregistered selection criterion. This is a bounded negative result: it does not prove that no operator family could select the indices. It does mean the current mass formula cannot be described as a spectral prediction.

Any new family must have an a-priori rationale and a new preregistration, with null-only power design completed before target evaluation. Re-running the same search on the same four targets would increase the look-elsewhere burden rather than resolve it.

## Audit records

- [Binding preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Cumulative protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Methodological write-up](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md)
- [Protocol data and code](https://github.com/RFT-SIRM/Phi-Genesis/tree/main/protocol_data)

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
