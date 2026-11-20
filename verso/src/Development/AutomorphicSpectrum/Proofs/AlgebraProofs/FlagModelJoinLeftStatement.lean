import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinLeft
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSub
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagModelJoinLeft.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.flag_model_join_left : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinLeftAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinLeft.main <;> assumption)
