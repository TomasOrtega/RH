import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCommutesSeparableHolds
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormCommutesSeparableHolds.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.norm_commutes_separable_holds : PositivityTheory.Rg.Tf.Loc.A1 → PositivityTheory.Rg.Tf.Loc.A2 := by
  first | exact @GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | exact GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable | (intros; apply GlobalTheory.CompanionTheory.TfLoc.norm_commutes_of_separable <;> assumption)
