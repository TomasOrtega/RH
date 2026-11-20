import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWhittakerLinearity.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.whittaker_linearity : Ad3.SchwartzSpaceL2.SLin := by
  first | exact @GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat | exact GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat | (intros; apply GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat <;> assumption)
