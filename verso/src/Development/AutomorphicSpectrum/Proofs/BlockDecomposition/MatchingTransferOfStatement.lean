import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.MatchT
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.MatchPow.matchTOf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMatchingTransferOf.lean&line=494#L494)
-/
theorem _root_.GlobalTheory.T.matching_transfer_of : MatchTOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPow.matchTOf | exact GlobalTheory.CompanionTheory.MatchPow.matchTOf | (intros; apply GlobalTheory.CompanionTheory.MatchPow.matchTOf <;> assumption)
