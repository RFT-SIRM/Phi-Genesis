"""Audit: is index 1 a trivial/near-universal gap-selection artifact on
the REAL Sierpinski gasket, independent of any applied potential/flux?

This directly extends the carpet look-elsewhere audit
(test_carpet_lookelsewhere.py) to the model's actual core substrate.
It matters much more here: the carpet branch was already abandoned,
but the SG + Mobius pi-flux search is THIS repo's central result
(README section 2-3), and mu <-> n=1 is presented as one of the
fit's four matches.

METHOD: same ratio-based gap-selection rule used throughout this repo
(top-k largest ratio jumps within the lowest `window` nonzero
eigenvalues), applied to hundreds/thousands of random on-site
potentials on the plain SG graph Laplacian (no flux, no Mobius
twists -- a generic perturbation, structurally analogous to what a
twist/flux search explores).

If index 1 (or any other target index) appears at a high rate
independent of the specific perturbation, its appearance in ANY
particular search (Mobius twist, scalar potential, carpet oscillator)
carries little evidential weight on its own -- it is what you would
see even from an unrelated random perturbation.
"""
import numpy as np

from .sg_laplacian import sierpinski_graph


def spectrum_with_potential(coords, E, potential=None):
    n = len(coords)
    L = np.zeros((n, n))
    deg = np.zeros(n)
    for a, b in E:
        L[a, b] = -1
        L[b, a] = -1
        deg[a] += 1
        deg[b] += 1
    for i in range(n):
        L[i, i] = deg[i]
        if potential is not None:
            L[i, i] += potential[i]
    return np.sort(np.linalg.eigvalsh(L))


def gap_selected_indices(spectrum, k=12, window=60):
    """Same ratio-based rule used for the carpet audit and consistent
    with this repo's gap-structure methodology: indices right after
    the k largest ratio jumps within the lowest `window` nonzero
    eigenvalues."""
    nz = spectrum[spectrum > 1e-8][:window]
    ratios = nz[1:] / nz[:-1]
    top = np.argsort(ratios)[::-1][:k]
    return sorted((top + 1).tolist())


def random_potential_hit_rates(level, target_indices, n_trials, seed=0,
                                freq_range=(0.5, 8.0), scale_range=(0.2, 3.0)):
    """Runs n_trials random oscillatory on-site potentials on the SG at
    the given level, and returns {index: hit_rate} for each index in
    target_indices -- the marginal (unconditional) rate at which that
    index appears in the gap-selected set, independent of what the
    potential actually is."""
    V, E, _ = sierpinski_graph(level)
    coords = np.array(V)
    x, y = coords[:, 0], coords[:, 1]
    rng = np.random.default_rng(seed)

    hits = {idx: 0 for idx in target_indices}
    for _ in range(n_trials):
        freq = rng.uniform(*freq_range)
        scale = rng.uniform(*scale_range)
        phase = rng.uniform(0.0, 2 * np.pi)
        a, b = rng.normal(size=2)
        pot = scale * np.sin(freq * (a * x + b * y) + phase)
        spec = spectrum_with_potential(coords, E, pot)
        sel = set(gap_selected_indices(spec))
        for idx in target_indices:
            if idx in sel:
                hits[idx] += 1

    return {idx: hits[idx] / n_trials for idx in target_indices}
