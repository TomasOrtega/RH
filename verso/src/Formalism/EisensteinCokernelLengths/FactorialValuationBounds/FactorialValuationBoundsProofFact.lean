import Mathlib
import Formalism.FrobeniusContraction.HighestWeightResidueAvoids
import Formalism.WindowSums.PowerSeriesRelationList
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.FiniteCocyclesLeCocycles
import Formalism.FrobeniusContraction.EulerC
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LemmaS

namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers.
-/
theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
