import Mathlib.Analysis.Calculus.Deriv.Add

namespace PhiGenesis.SpectralGap

/-- Isolated check: negation of a scalar real-valued derivative. -/
theorem derivativeNegScratch
    (f : ℝ → ℝ) (x f' : ℝ)
    (hf : HasDerivAt f f' x) :
    HasDerivAt (-f) (-f') x := by
  exact hf.neg

/-- Isolated check: subtraction of scalar real-valued derivatives. -/
theorem derivativeSubScratch
    (f g : ℝ → ℝ) (x f' g' : ℝ)
    (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (f - g) (f' - g') x := by
  exact hf.sub hg

end PhiGenesis.SpectralGap
