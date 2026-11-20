import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.capelli_operator_unitaryGroup_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)
