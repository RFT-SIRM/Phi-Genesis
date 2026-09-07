"""Fast test: top-quark consistency audit.

The README's "Integer mass formula" section reports a 4-fermion fit
(mu, tau, charm, bottom; n = {1,12,17,40}, A = 104.63 MeV, mean error
0.68%) and separately reports a "numerological" relation
    n_t = v / (sqrt(2) * A) ~= 1680 = 8 * 7#  (7-primorial = 2*3*5*7)
for the top quark, used historically as suggestive evidence for the
EWSB-scale interpretation of A.

HONEST FINDING (this test documents it, not just prose): these two
parts of the repo are NOT mutually consistent under the CURRENT fitted
scale A = 104.63 MeV:

  - n_t = 1680 was computed under an OLDER value of A (~103.63 MeV),
    not the current one.
  - Recomputing n_t = v/(sqrt(2)*A) with the CURRENT A = 104.63 MeV
    gives ~1664, not 1680 -- the "8 * 7#" coincidence does not survive
    the scale update.
  - The best INTEGER fit to the actual top mass at A = 104.63 MeV is
    n = 1654 (error ~0.02%) -- close to neither 1680 nor the
    formula-predicted 1664.
  - Using n = 1680 (the number actually advertised) with A = 104.63
    gives a top-quark error of ~1.55% -- more than double the 4-fermion
    mean of 0.68%. This is very likely WHY the top quark does not
    appear in the "Integer mass formula" table: including it would
    raise the reported mean error from 0.68% to ~0.85%, i.e. back up
    to the level of the "old fitted decimals" that the integer fit is
    specifically presented as improving on.

This test does not "fix" the physics -- there is no single correct
n_t to assert here, because the whole point is that the three
candidate values disagree. It exists so this inconsistency cannot
silently disappear again if someone edits mass_check.py or the README
without noticing it.
"""
import numpy as np

from phi_genesis.mass_check import EXPERIMENTAL, PHI

A_CURRENT = 104.63          # the scale actually used in the README's integer fit
A_OLD = 103.63               # the scale n_t=1680 was historically computed under
V_EV = 246220.0
N_T_ADVERTISED = 1680        # the "8 * 7#" number that appears in the repo


def test_advertised_nt_does_not_match_current_A():
    """n_t = v/(sqrt(2)*A) at the CURRENT A should NOT reproduce 1680 --
    if it ever does, someone has changed A back, or the relationship
    has been re-derived, and this test's premise needs revisiting."""
    n_t_at_current_A = V_EV / (np.sqrt(2) * A_CURRENT)
    assert abs(n_t_at_current_A - N_T_ADVERTISED) > 5, (
        f"n_t at current A ({n_t_at_current_A:.1f}) is now close to the "
        f"advertised {N_T_ADVERTISED} -- if A or the formula changed to "
        f"make these agree, update this test's docstring/assertion, "
        f"this would actually be GOOD news worth documenting properly."
    )


def test_top_quark_error_with_advertised_nt_exceeds_four_fermion_mean():
    """Using the advertised n_t=1680 at the current A=104.63, the top
    quark's error should exceed the reported 4-fermion mean (0.68%) --
    documenting why it is plausible the table omits it, rather than
    letting that omission go unexamined."""
    m_pred = A_CURRENT * N_T_ADVERTISED
    err_pct = 100 * abs(m_pred - EXPERIMENTAL["top"]) / EXPERIMENTAL["top"]
    four_fermion_mean = 0.68
    print(f"\n[top-quark audit] n_t={N_T_ADVERTISED}, A={A_CURRENT} -> "
          f"predicted={m_pred:.1f} MeV, exp={EXPERIMENTAL['top']} MeV, "
          f"error={err_pct:.3f}% (4-fermion mean: {four_fermion_mean}%)")
    assert err_pct > four_fermion_mean


def test_best_fit_nt_disagrees_with_both_other_candidates():
    """The integer n_t that best fits the ACTUAL top mass at the
    current A should differ from both 1680 (advertised) and the
    formula-predicted value at current A -- three genuinely different
    numbers, not measurement noise around one true value."""
    n_best = round(EXPERIMENTAL["top"] / A_CURRENT)
    n_formula_current = round(V_EV / (np.sqrt(2) * A_CURRENT))
    print(f"\n[top-quark audit] three candidate n_t values: "
          f"advertised={N_T_ADVERTISED}, "
          f"formula@current_A={n_formula_current}, "
          f"best_fit@current_A={n_best}")
    assert len({N_T_ADVERTISED, n_formula_current, n_best}) == 3, (
        "expected three genuinely distinct candidate values for n_t "
        "-- if two now coincide, the inconsistency this test guards "
        "against may have been resolved (good!) or the numbers moved "
        "again (needs review either way)."
    )
