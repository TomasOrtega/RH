import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanNefCriteriaHold
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FKleimanNefCriteriaHold.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.kleiman_nef_criteria_hold : KleimanNefIntersectionNonneg ∧ KleimanNefFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | exact GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.kleimanNef_field_and_fibre <;> assumption)
