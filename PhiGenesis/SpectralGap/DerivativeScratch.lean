import Mathlib.Analysis.Calculus.Deriv.Basic

namespace PhiGenesis.SpectralGap

/-- Isolated check: negation of a scalar real-valued derivative. -/
theorem derivativeNegScratch
    (f : ℝ → ℝ) (x f' : ℝ)
    (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => -f y) (-f') x := by
  simpa using hf.neg

/-- Isolated check: subtraction of scalar real-valued derivatives. -/
theorem derivativeSubScratch
    (f g : ℝ → ℝ) (x f' g' : ℝ)
    (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y - g y) (f' - g') x := by
  simpa using hf.sub hg

end PhiGenesis.SpectralGap
