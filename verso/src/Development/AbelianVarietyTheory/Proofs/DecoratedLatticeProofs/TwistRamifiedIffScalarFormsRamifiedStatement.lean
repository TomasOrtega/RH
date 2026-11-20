import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistRamifiedIffScalarFormsRamified
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.twistRamified_iff_scalarFormsRamified : GlobalTheory.AdForm.TwRam' := by
  first | exact @GlobalTheory.AdForm.ram_iff_scalar_ram | exact GlobalTheory.AdForm.ram_iff_scalar_ram | (intros; apply GlobalTheory.AdForm.ram_iff_scalar_ram <;> assumption)
