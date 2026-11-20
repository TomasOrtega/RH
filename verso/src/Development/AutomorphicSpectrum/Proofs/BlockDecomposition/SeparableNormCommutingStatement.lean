import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableNormCommuting
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Centraliser.a1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSeparableNormCommuting.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.separable_norm_commuting : PositivityTheory.Rg.Tf.Loc.A1 := by
  first | exact @GlobalTheory.CompanionTheory.Centraliser.a1 | exact GlobalTheory.CompanionTheory.Centraliser.a1 | (intros; apply GlobalTheory.CompanionTheory.Centraliser.a1 <;> assumption)
