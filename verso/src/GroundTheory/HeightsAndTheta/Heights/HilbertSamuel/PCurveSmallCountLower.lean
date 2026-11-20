import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCurveSmallCountLower
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCurveCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveSmallCountLower

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem statement_iff : CurveSmallCountLower.Statement ↔ Targets.CurveCountLower.Statement :=
  Iff.rfl

end CurveSmallCountLower

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CurveSmallCountLower.proof (hD : Targets.CurveDegreeVert.Statement) (hV : Targets.CurveVertIndex.Statement)
    (hL : Targets.CurveIndexLinear.Statement) (hN : Targets.CurveBoxCount.Statement) :
    CurveSmallCountLower.Statement :=
  CurveSmallCountLower.statement_iff.mpr (Targets.CurveCountLower.proof hD hV hL hN)

end GroundTheory.Heights₂.Heights.HilbertSamuel
