import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.NefLineBundleNumericalTheoremsProof
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.nefLineBundleNumericalTheorems_proof : GlobalTheory.Published.NefNumerics := by
  first | exact @GlobalTheory.nefNumerics_outright | exact GlobalTheory.nefNumerics_outright | (intros; apply GlobalTheory.nefNumerics_outright <;> assumption)
