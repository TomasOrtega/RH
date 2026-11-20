import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WhittakerTrans.sTrans` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerRightTranslation.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.whittaker_right_translation : Ad3.SchwartzSpaceL2.STrans := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | exact GlobalTheory.CompanionTheory.WhittakerTrans.sTrans | (intros; apply GlobalTheory.CompanionTheory.WhittakerTrans.sTrans <;> assumption)
