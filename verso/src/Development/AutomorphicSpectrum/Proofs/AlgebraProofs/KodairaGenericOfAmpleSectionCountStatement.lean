import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FKodairaGenericOfAmpleSectionCount.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.kodaira_generic_of_ample_section_count : VeryAmpleNefPlusAmple.Statement → SectionCount.Statement → GroundTheory.Heights₂.Heights.HilbertSamuel.KodairaGeneric.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | exact GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count | (intros; apply GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count <;> assumption)
