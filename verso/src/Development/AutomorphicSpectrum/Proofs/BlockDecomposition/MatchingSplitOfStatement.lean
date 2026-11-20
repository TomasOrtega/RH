import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchingSplitOf.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | exact GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | (intros; apply GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf <;> assumption)
