import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.matching_identity_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)
