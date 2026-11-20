import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DensityAndRegions
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.ShortIntervalPrimes

namespace GlobalTheory.ZerosNearOne

/- English proof (translation)
Take `⟨C, c, hC, hc, H⟩` from `density_and_regions`. Conclude with `⟨C, c, hC, hc, fun _ => H⟩`.
-/
theorem main : ∃ C1 c : ℝ, 0 < C1 ∧ 0 < c ∧ ∀ D : D7, adm6 D C1 c := by
  obtain ⟨C, c, hC, hc, H⟩ := density_and_regions
  exact ⟨C, c, hC, hc, fun _ => H⟩

end GlobalTheory.ZerosNearOne
