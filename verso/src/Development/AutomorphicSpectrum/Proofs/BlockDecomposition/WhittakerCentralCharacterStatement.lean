import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCentralCharacter
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerCentralCharacter.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.whittaker_central_character : Ad3.SchwartzSpaceL2.SCen := by
  first | exact @GlobalTheory.CompanionTheory.WhittakerCentral.sCen | exact GlobalTheory.CompanionTheory.WhittakerCentral.sCen | (intros; apply GlobalTheory.CompanionTheory.WhittakerCentral.sCen <;> assumption)
