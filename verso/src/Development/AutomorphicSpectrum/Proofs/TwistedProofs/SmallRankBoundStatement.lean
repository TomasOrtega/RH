import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.SmallRankBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.InertZeta.smallRank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FSmallRankBound.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.small_rank_bound : SmallRank := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.smallRank | exact GlobalTheory.CompanionTheory.InertZeta.smallRank | (intros; apply GlobalTheory.CompanionTheory.InertZeta.smallRank <;> assumption)
