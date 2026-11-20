import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
