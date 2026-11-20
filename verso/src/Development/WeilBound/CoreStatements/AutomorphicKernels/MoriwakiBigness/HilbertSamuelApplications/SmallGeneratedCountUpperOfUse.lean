import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArithKleiman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite

namespace PositivityTheory.MbHsUse

open GroundTheory.Heights₂.Heights.HilbertSamuel

def HSUse : Prop :=
  ArithKleiman.Statement ∧ G7.Statement ∧ ArithmeticVolumeNef.Statement

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HSUse.g7 (h : HSUse) : G7.Statement := h.2.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HSUse.g7p (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticHilbertSamuelUpperBound := h.2.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HSUse.z1 (h : HSUse) : ReciprocityTheory.ChartRestriction.G.Geo.SuccessiveMinimaLowerBound :=
  G5.proof' h.1 CurvePointsFinite.proof

end PositivityTheory.MbHsUse

namespace GlobalTheory.CompanionTheory.Ar.Giv

end GlobalTheory.CompanionTheory.Ar.Giv

namespace GlobalTheory.CompanionTheory.Ar.Small

end GlobalTheory.CompanionTheory.Ar.Small
