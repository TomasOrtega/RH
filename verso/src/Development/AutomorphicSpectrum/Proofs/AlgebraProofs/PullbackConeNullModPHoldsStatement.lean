import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FPullbackConeNullModPHolds.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)
