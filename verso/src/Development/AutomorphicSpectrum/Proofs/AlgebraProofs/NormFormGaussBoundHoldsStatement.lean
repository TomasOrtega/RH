import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHolds
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.norm_form_gauss_bound_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.NormFormGaussBound.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | exact GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.normFormGaussBound <;> assumption)
