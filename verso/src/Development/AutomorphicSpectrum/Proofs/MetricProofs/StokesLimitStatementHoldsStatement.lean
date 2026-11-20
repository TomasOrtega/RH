import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.StokesLimitStatementHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesLimitTVb
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.stokes_limit_statement_holds : GroundTheory.Heights₂.Heights.LowerBoundFree.StokesLimitTVb.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb | exact GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.VbLimit.stokesLimitTVb <;> assumption)
