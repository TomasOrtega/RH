import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchingWordOf.lean&line=201#L201)
-/
theorem _root_.GlobalTheory.T.matching_word_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf | exact GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf | (intros; apply GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf <;> assumption)
