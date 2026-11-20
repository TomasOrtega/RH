import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adelicUnitaryHaar_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FAdelicUnitaryGroupHaarPropertiesProof.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)
