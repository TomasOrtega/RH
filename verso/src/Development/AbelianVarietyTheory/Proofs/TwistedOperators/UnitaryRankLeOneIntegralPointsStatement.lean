import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FUnitaryRankLeOneIntegralPoints.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.unitary_rank_le_one_integral_points : SmallRank := by
  first | exact @GlobalTheory.InertZeta.smallRank | exact GlobalTheory.InertZeta.smallRank | (intros; apply GlobalTheory.InertZeta.smallRank <;> assumption)
