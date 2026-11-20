import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  first | exact @GlobalTheory.LocalConst.constC | exact GlobalTheory.LocalConst.constC | (intros; apply GlobalTheory.LocalConst.constC <;> assumption)
