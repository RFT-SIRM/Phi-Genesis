"""Exhaustive partial-flux selection-rule search on SG.

At level 5 there are 5 hole generations (81/27/9/3/1 holes).
Twisting by generation gives 2^5 = 32 configurations.

RESULT: max simultaneous hits on {1,12,17,40} = 1 of 4.
Index 40 never appears as gap-selected under any configuration.
This closes the twist-by-generation family as a selection rule.

Open Problem #1 remains open beyond this family.
"""
import itertools
import numpy as np
from mobius import mobius_spectrum, gap_selected_indices

TARGET_INDICES = {1, 12, 17, 40}


def exhaustive_twist_search(level=5, k_gaps=8):
    """Returns dict: combo -> (selected_indices, hits)."""
    results = {}
    for r in range(6):
        for combo in itertools.combinations(range(1, 6), r):
            spec = mobius_spectrum(level, twist_levels=set(combo))
            sel = set(gap_selected_indices(spec, k=k_gaps))
            results[combo] = (sel, sel & TARGET_INDICES)
    return results


def search_summary(results):
    max_hits = max(len(h) for _, h in results.values())
    idx40_any = any(40 in s for s, _ in results.values())
    per_index = {i: [] for i in TARGET_INDICES}
    for combo, (sel, hit) in results.items():
        for i in hit:
            per_index[i].append(combo)
    return {
        "max_simultaneous_hits": max_hits,
        "index_40_ever_selected": idx40_any,
        "configs_hitting_each_index": {i: len(v) for i, v in per_index.items()},
    }
