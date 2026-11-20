import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MatchId.matchLMIdOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchingIdentityOf.lean&line=283#L283)
-/
theorem _root_.GlobalTheory.T.matching_identity_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)
