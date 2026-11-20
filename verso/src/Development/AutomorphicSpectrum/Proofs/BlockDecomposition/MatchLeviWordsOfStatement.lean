import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchLeviWordsOf.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
