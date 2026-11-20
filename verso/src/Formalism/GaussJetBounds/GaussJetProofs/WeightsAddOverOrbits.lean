import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
import Formalism.IncomingBounds.WeightIdentities

noncomputable section
open scoped BigOperators

universe u v w

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

/- English proof (translation)
Unfold `dot`. Conclude with `Finsupp.sum_fintype _ _ (by simp)`.
-/
theorem coreL_dot_fintype {ι : Type v} [Fintype ι] (n : ι →₀ ℕ) (r : ι → ℝ) :
    dot n r = ∑ i, (n i : ℝ) * r i := by
  unfold dot
  exact Finsupp.sum_fintype _ _ (by simp)

end Formalism.DworkPowerSeriesWeights
