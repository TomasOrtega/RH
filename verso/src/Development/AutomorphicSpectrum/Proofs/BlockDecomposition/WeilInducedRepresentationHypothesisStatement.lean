import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WeilPiRep.wPiRep` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilInducedRepresentationHypothesis.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.weil_induced_representation_hypothesis : Ad3.K.GL2LocalData.WPiRep := by
  first | exact @GlobalTheory.CompanionTheory.WeilPiRep.wPiRep | exact GlobalTheory.CompanionTheory.WeilPiRep.wPiRep | (intros; apply GlobalTheory.CompanionTheory.WeilPiRep.wPiRep <;> assumption)
