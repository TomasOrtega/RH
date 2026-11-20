import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupHaarPropertiesProof
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)
