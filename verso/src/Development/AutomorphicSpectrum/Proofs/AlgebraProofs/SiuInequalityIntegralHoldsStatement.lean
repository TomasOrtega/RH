import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SiuInequalityIntegralHolds
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.siuZ` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FSiuInequalityIntegralHolds.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.siu_inequality_integral_holds : SiuZStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.siuZ | exact GlobalTheory.CompanionTheory.Ar.Giv.siuZ | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.siuZ <;> assumption)
