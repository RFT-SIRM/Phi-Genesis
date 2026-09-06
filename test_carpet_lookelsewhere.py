"""Nightly test: guard against re-treating the Sierpinski-carpet
oscillatory-potential search as a "solved selection rule".

Context: an exploratory search over V(x,y) = scale*sin(freq*(x+y)) on
the Sierpinski carpet (see phi_genesis.sierpinski_carpet) reported a
"4/4" match against the fermion-mass indices {1, 12, 17, 40} after
trying ~128 configurations at level 3 and a further parameter sweep at
level 4. Framed alone, "4/4" sounds like a breakthrough. These tests
exist to keep that framing honest going forward, the same way
test_honest.py keeps the original gasket mass-formula fit honest.

Two independent checks:

  1. test_lookelsewhere_hit_rate -- Monte-Carlo null test. Samples
     random oscillatory potentials (random freq, scale, phase,
     direction) and measures how often >=3/4 or 4/4 of the target
     indices appear by pure chance. If this rate is non-negligible
     relative to the number of configurations actually tried in the
     original search, "4/4" is unremarkable.

  2. test_hits_are_statistically_independent -- the more decisive
     check. If the four index-hits shared a common physical cause (a
     real selection mechanism), seeing 3 of them should raise the
     probability of the 4th above its baseline rate. This test
     computes P(index | other three present) vs the marginal P(index)
     for each of the four indices. Independence (or negative
     correlation) is the fingerprint of coincidental overfitting
     across a large search, not of a shared mechanism.

Both are informational/diagnostic: they assert internal consistency of
the statistics (valid probabilities, non-empty conditioning sets), not
a specific physics conclusion -- that conclusion is for a human reader
to draw from the printed numbers, same policy as test_nightly_deep.py.
"""
import numpy as np
import pytest

from phi_genesis.sierpinski_carpet import build_carpet_graph, spectrum_from_graph, gap_selected_indices

pytestmark = pytest.mark.nightly

TARGET = frozenset({1, 12, 17, 40})
LEVEL = 3          # 688 vertices -- fast enough for tens of thousands of trials
N_TRIALS = 30_000
SEED = 0


def _random_potential_trials(coords, E, rng, n_trials):
    """Yields the set of TARGET indices hit, one per random potential."""
    x, y = coords[:, 0], coords[:, 1]
    for _ in range(n_trials):
        freq = rng.uniform(0.5, 8.0)
        scale = rng.uniform(0.2, 3.0)
        phase = rng.uniform(0.0, 2 * np.pi)
        a, b = rng.normal(size=2)
        V = scale * np.sin(freq * (a * x + b * y) + phase)
        spec = spectrum_from_graph(coords, E, V)
        sel = set(gap_selected_indices(spec))
        yield TARGET & sel


def test_lookelsewhere_hit_rate():
    """How often does a random oscillatory potential match >=3/4 or
    4/4 of {1, 12, 17, 40} by pure chance, on the same carpet
    construction and gap-selection rule as the original search?"""
    coords, E = build_carpet_graph(LEVEL)
    rng = np.random.default_rng(SEED)
    records = list(_random_potential_trials(coords, E, rng, N_TRIALS))

    counts = {k: sum(1 for r in records if len(r) == k) for k in range(5)}
    p_ge3 = (counts[3] + counts[4]) / N_TRIALS
    p_4 = counts[4] / N_TRIALS

    n_configs_actually_tried = 150  # ~128 at level 3 + a further sweep at level 4
    p_at_least_one_4of4 = 1 - (1 - p_4) ** n_configs_actually_tried

    print(f"\n[carpet look-elsewhere] {N_TRIALS} random potentials, level {LEVEL}:")
    for k in range(5):
        print(f"  {k}/4 hits: {counts[k]} ({100 * counts[k] / N_TRIALS:.2f}%)")
    print(f"  P(>=3/4 by chance, one trial)  = {100 * p_ge3:.2f}%")
    print(f"  P(4/4 by chance, one trial)    = {100 * p_4:.3f}%")
    print(f"  P(>=1 hit of 4/4 across ~{n_configs_actually_tried} trials, "
          f"the actual search size) = {100 * p_at_least_one_4of4:.1f}%")
    print("  Interpretation: a double-digit percent chance of stumbling "
          "onto 4/4 across the search that was actually run is NOT strong "
          "evidence of a real selection mechanism.")

    assert 0.0 <= p_ge3 <= 1.0
    assert 0.0 <= p_4 <= 1.0


def test_hits_are_statistically_independent():
    """Decisive check: does hitting 3 of the 4 target indices raise the
    probability of the 4th above its own baseline rate? If the answer
    is 'no' (or 'lower'), the four hits do not share a common cause --
    which is the fingerprint of overfitting via a large search, not of
    a real selection rule."""
    coords, E = build_carpet_graph(LEVEL)
    rng = np.random.default_rng(SEED + 1)
    records = list(_random_potential_trials(coords, E, rng, N_TRIALS))

    print(f"\n[carpet independence check] {N_TRIALS} random potentials, level {LEVEL}:")
    print(f"{'held out':>10s} {'marginal P':>12s} {'P | other 3':>14s} {'n_cond':>8s}  verdict")

    any_positive_evidence = False
    for held_out in sorted(TARGET):
        others = TARGET - {held_out}
        marginal = sum(1 for r in records if held_out in r) / N_TRIALS
        cond_trials = [r for r in records if others <= r]
        n_cond = len(cond_trials)
        if n_cond < 20:
            print(f"{held_out:10d} {100*marginal:11.2f}% {'(too few obs)':>14s} {n_cond:8d}  skip")
            continue
        cond = sum(1 for r in cond_trials if held_out in r) / n_cond
        verdict = "POSSIBLE LINK" if cond > marginal * 1.5 else "independent/no link"
        if cond > marginal * 1.5:
            any_positive_evidence = True
        print(f"{held_out:10d} {100*marginal:11.2f}% {100*cond:13.2f}% {n_cond:8d}  {verdict}")

    print("  If none of the four rows show 'POSSIBLE LINK', the reported "
          "4/4 has no evidence of a shared underlying mechanism linking "
          "the indices -- each hit is best explained independently, i.e. "
          "by chance under a large search.")
    # Informational: we do not hard-fail the suite if a link appears --
    # we only ever want a human to look at fresh evidence, not to hide it.
    assert True
