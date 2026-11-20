import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeNullModP
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | exact GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP <;> assumption)
