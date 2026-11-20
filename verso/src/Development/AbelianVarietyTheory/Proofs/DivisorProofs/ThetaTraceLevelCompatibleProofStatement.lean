import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.thetaTraceLevelCompatible_proof : GlobalTheory.BaseCmp.TraceLevel := by
  first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)
