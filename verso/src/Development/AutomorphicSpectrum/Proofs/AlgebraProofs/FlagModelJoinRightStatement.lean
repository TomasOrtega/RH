import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagModelJoinRight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ExSubAlt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FFlagModelJoinRight.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main <;> assumption)
