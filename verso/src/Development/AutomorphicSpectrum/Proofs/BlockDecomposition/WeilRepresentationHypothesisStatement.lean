import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationHypothesis
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeilRepresentationHypothesis.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.weil_representation_hypothesis : Ad3.K.GL2LocalData.WRep := by
  first | exact @GlobalTheory.CompanionTheory.GL2LocalData.wRep | exact GlobalTheory.CompanionTheory.GL2LocalData.wRep | (intros; apply GlobalTheory.CompanionTheory.GL2LocalData.wRep <;> assumption)
