import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
