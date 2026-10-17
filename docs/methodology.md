# Methodology — Testing Spectral Selection Rules

![RFT-SIRM](https://img.shields.io/badge/RFT--SIRM-Research-174ea6?style=flat-square) ![Phi-Genesis](https://img.shields.io/badge/Phi--Genesis-Spectral%20Research-147fba?style=flat-square) ![Evidence standard](https://img.shields.io/badge/standard-evidence--first-168f83?style=flat-square)


This page explains the method used to test whether spectral configurations select the target indices \(T=\{1,12,17,40\}\). The full versioned protocol is maintained in [METHODOLOGY.md](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/METHODOLOGY.md); the cumulative record is the [protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md).

## The question and the look-elsewhere effect

The mass formula \(m=A n\) fits four selected masses with one scale and four integer indices. The central research question is not whether the fit can be written down, but whether a spectral rule independently selects those indices. Trying many operator configurations makes accidental matches increasingly likely.

The protocol therefore asks whether a configuration scores unusually well relative to null ensembles **after taking the maximum over the tested configurations**. A striking individual match is not enough.

## Protocol design

1. **Fix the target and rule.** Record the target set, index-selection rule, spectral window and tested family before evaluation.
2. **Define null ensembles.** Use generic operators of the relevant type to estimate how often each target appears by chance.
3. **Weight by base rate.** Common targets should contribute less evidence than rare targets.
4. **Correct for searching many configurations.** The test statistic uses the best score across the family, not just a hand-picked configuration.
5. **Check power using null data alone.** Confirm that the chosen statistic and threshold can be reached before evaluating the target family.
6. **Use a fixed decision threshold.** A candidate must reach \(p\le0.01\) under both specified null ensembles.
7. **Keep a cumulative ledger.** Record abandoned, exploratory and related families, and disclose dependence between them.

## Why the power check matters

Protocol v1.0 was unable to reach the decision threshold even if a configuration selected all four targets. Its negative outcome therefore did not meaningfully discriminate the tested family. Later protocols changed \(k\) using null-only design so that the threshold could be reached. Those later tests still did not pass.

## Interpretation discipline

A negative result applies to the tested family, selection rule, parameter range and null model. It does not prove that no mechanism can exist. Conversely, a numerical match after choosing targets and trying many configurations is not a prediction.

## Primary records

- [Binding preregistration v1.2.1](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/PREREGISTRATION_v1.2.1.md)
- [Protocol ledger](https://github.com/RFT-SIRM/Phi-Genesis/blob/main/protocol_ledger.md)
- [Selection protocol results](selection-protocol.md)
- [Reproduction commands](reproducibility.md)

---

<div class="phi-doc-nav">
<strong>Explore Phi-Genesis</strong><br>
<a href="https://rft-sirm.github.io/Phi-Genesis/interactive/">Interactive portal</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/research-map.html">Research map</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/verified-results.html">Verified results</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/open-problems.html">Open problems</a> · <a href="https://rft-sirm.github.io/Phi-Genesis/reproducibility.html">Reproducibility</a> · <a href="https://github.com/RFT-SIRM/Evgeny-s-Theory-of-Everything/blob/main/DISSERTATION.md">Dissertation</a> · <a href="https://github.com/RFT-SIRM/Phi-Genesis">Source repository</a>
</div>
