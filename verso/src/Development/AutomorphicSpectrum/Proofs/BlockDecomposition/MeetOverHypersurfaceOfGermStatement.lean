import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeetOverHypersurfaceOfGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermMeetOverHypersurface
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteFibreGermIntegral
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMeetOverHypersurfaceOfGerm.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.meet_over_hypersurface_of_germ : FiniteFibreGermIntegral.Statement → IrreducibleGermMeetOverHypersurface.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral <;> assumption)
