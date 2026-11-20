import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTraceLevelCompatibleProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceLevelPf.traceLevel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaTraceLevelCompatibleProof.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.thetaTraceLevelCompatible_proof : GlobalTheory.BaseCmp.TraceLevel := by
  first | exact @GlobalTheory.TraceLevelPf.traceLevel | exact GlobalTheory.TraceLevelPf.traceLevel | (intros; apply GlobalTheory.TraceLevelPf.traceLevel <;> assumption)
