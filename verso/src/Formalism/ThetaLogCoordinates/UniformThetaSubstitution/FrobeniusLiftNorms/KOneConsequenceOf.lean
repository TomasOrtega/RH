import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FirstDeriv
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.CoeffSubstLgFOfDegreeOne

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)

namespace FormalGroupLawNegation

open FormalGroupLaws

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem integral_X {K ι : Type} [NormedField K] (x : ι) :
    Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem integral_neg {K ι : Type} [NormedField K] {f : MvPowerSeries ι K} (hf : Integral f) :
    Integral (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n

end FormalGroupLawNegation

open FormalGroupLawNegation FormalGroupLaws

end Formalism.InvariantFactorPaths.G7
