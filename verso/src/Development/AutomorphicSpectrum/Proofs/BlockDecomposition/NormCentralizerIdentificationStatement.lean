import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormCentralizerIdentification
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FNormCentralizerIdentification.lean&line=254#L254)
-/
theorem _root_.GlobalTheory.T.norm_centralizer_identification : PositivityTheory.Rg.Tf.Loc.A2 → PositivityTheory.Rg.Tf.Loc.A3 := by
  first | exact @GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | exact GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma | (intros; apply GlobalTheory.CompanionTheory.CyclicCocycle.cyclicCocycleLemma <;> assumption)
