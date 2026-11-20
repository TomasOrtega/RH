import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationFinite
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CurveNormalisationFiniteLemmas
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem CurveNormalisationFinite.proof (hN : FieldNumbers.NoetherIntegralClosureFinite.Statement.{0}) :
    CurveNormalisationFinite.Statement := by
  intro n I q hI
  have := isReduced_curveLocalRing I q hI
  exact finite_integralClosure_of_isReduced hN (algebraMap _ (curveLocalRing I q)) (curveLocalRing_eq_div I q)

end GroundTheory.Heights₂.Heights
