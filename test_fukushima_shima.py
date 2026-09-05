from phi_genesis.fukushima_shima import gap_structure_check

def test_gap_structure():
    ok, pos, sizes = gap_structure_check(6)
    assert ok, f"gaps not at fixed points: {pos}"
