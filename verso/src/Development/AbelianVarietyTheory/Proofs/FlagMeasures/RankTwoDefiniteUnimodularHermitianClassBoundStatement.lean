import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FRankTwoDefiniteUnimodularHermitianClassBound.lean&line=225#L225)
-/
theorem _root_.GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound : RankTwoClasses := by
  first | exact @GlobalTheory.RankTwoCount.rankTwoClasses | exact GlobalTheory.RankTwoCount.rankTwoClasses | (intros; apply GlobalTheory.RankTwoCount.rankTwoClasses <;> assumption)
