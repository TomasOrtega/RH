import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchingUnitOf.lean&line=192#L192)
-/
theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
