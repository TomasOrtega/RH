import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.QuotU.h2U` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnipotentHeckeSupport.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.unipotent_hecke_support : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  first | exact @GlobalTheory.CompanionTheory.QuotU.h2U | exact GlobalTheory.CompanionTheory.QuotU.h2U | (intros; apply GlobalTheory.CompanionTheory.QuotU.h2U <;> assumption)
