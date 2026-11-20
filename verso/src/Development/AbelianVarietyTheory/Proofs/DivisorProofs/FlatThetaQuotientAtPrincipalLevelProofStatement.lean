import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatThetaQuotientAtPrincipalLevelProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.flatThetaQuotientAtPrincipalLevel_proof : GlobalTheory.BaseCmp.FlatTwoStep := by
  first | exact @GlobalTheory.BaseCmp.flatTwoStep_holds | exact GlobalTheory.BaseCmp.flatTwoStep_holds | (intros; apply GlobalTheory.BaseCmp.flatTwoStep_holds <;> assumption)
