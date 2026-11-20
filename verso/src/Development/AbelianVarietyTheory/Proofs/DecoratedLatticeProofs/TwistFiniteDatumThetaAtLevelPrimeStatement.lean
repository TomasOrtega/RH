import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistFiniteDatumThetaAtLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.twistFiniteDatum_theta_at_levelPrime : GlobalTheory.AdForm.TwVec' := by
  first | exact @GlobalTheory.AdForm.twVec' | exact GlobalTheory.AdForm.twVec' | (intros; apply GlobalTheory.AdForm.twVec' <;> assumption)
