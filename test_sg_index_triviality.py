"""Fast test: does index 1 (and friends) appear trivially in the
gap-selected set on the REAL Sierpinski gasket, independent of the
applied potential?

Why this matters more than the analogous carpet check
(test_carpet_lookelsewhere.py): the SG + Mobius pi-flux search is
THIS repo's central result. README section 3 reports "max simultaneous
hits on {1,12,17,40}: 1 of 4" for the exhaustive Mobius twist search,
and section 4's mu <-> n=1 correspondence is one of the four points in
the headline mass fit. If index 1 shows up at a high rate under ANY
generic random perturbation (not just Mobius twists), then its
appearance in the twist search is not distinguishing evidence for
that specific mechanism -- it's what a gap-selection rule does anyway.

HONEST RESULT (verified against the real phi_genesis.sg_laplacian
code, level 5, 8000 random on-site potentials):
  - index 1:  ~95.6% of random trials  (near-universal -- NOT informative)
  - index 12: ~37.5%
  - index 17: ~22.2%
  - index 40: ~3.4%   (genuinely rare -- the only index whose
                        appearance in any search is worth taking
                        seriously as potential evidence)

This does not by itself disprove the pi-flux mechanism for index 17 or
40 -- but it does mean the "1 of 4" framing anywhere in this repo
should not silently count index 1 as if it were as significant a hit
as index 40 would be.
"""
import pytest

from phi_genesis.sg_index_triviality import random_potential_hit_rates

LEVEL = 5
TARGET = (1, 12, 17, 40)
N_TRIALS = 4000  # ~30s at level 5; fast enough for the regular suite


def test_index_one_is_not_a_meaningful_hit():
    """Index 1 should appear at a high rate under generic random
    potentials, unrelated to any specific selection mechanism. If this
    ever drops substantially, something about the gap-selection method
    or graph construction has changed and the 'index 1 is trivial'
    caveat needs re-evaluating (which would actually be informative:
    it would mean mu<->n=1 became more meaningful, not less)."""
    rates = random_potential_hit_rates(LEVEL, TARGET, N_TRIALS)
    print(f"\n[SG index-triviality] level {LEVEL}, {N_TRIALS} random potentials:")
    for idx in TARGET:
        print(f"  index {idx}: {100*rates[idx]:.2f}%")
    assert rates[1] > 0.8, (
        f"index 1 hit rate ({100*rates[1]:.1f}%) dropped well below the "
        f"~95% baseline -- re-examine whether the mu<->n=1 correspondence "
        f"is now more meaningful, or whether the gap-selection method "
        f"changed."
    )


def test_index_forty_is_genuinely_rare():
    """Unlike index 1, index 40 should be genuinely rare under random
    potentials -- meaning if a real search (Mobius, scalar potential,
    etc.) ever DOES select it, that specific result is worth taking
    seriously, unlike an index-1 hit."""
    rates = random_potential_hit_rates(LEVEL, TARGET, N_TRIALS, seed=1)
    assert rates[40] < 0.15, (
        f"index 40 hit rate ({100*rates[40]:.1f}%) is no longer rare -- "
        f"if a future search reports hitting index 40, this needs "
        f"re-checking against the (possibly changed) baseline rate "
        f"before treating it as meaningful."
    )
