import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnramifiedExtensionIntegralBasis.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.unramified_extension_integral_basis : PositivityTheory.Rg.Tf.Loc.D0a := by
  first | exact @GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | exact GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a | (intros; apply GlobalTheory.CompanionTheory.UnramDict.unramifiedDictionary_a <;> assumption)
