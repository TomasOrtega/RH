import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerSmoothness.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.whittaker_smoothness : Ad3.SchwartzSpaceL2.SSmooth := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | exact GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth | (intros; apply GlobalTheory.CompanionTheory.WhittakerSmooth.sSmooth <;> assumption)
