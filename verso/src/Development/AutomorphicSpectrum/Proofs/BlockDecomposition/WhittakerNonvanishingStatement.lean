import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNonvanishing
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WhNe.sNe` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerNonvanishing.lean&line=149#L149)
-/
theorem _root_.GlobalTheory.T.whittaker_nonvanishing : Ad3.SchwartzSpaceL2.SNe := by
  first | exact @GlobalTheory.CompanionTheory.WhNe.sNe | exact GlobalTheory.CompanionTheory.WhNe.sNe | (intros; apply GlobalTheory.CompanionTheory.WhNe.sNe <;> assumption)
