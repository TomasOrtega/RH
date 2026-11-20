import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CapelliLocality.capelliH_local` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCapelliOperatorUnitaryGroupLocal.lean&line=82#L82)
-/
theorem _root_.GlobalTheory.T.capelli_operator_unitaryGroup_local : PI.UnitaryGroupMassFormula.CapelliEig.Loc := by
  first | exact @GlobalTheory.CapelliLocality.capelliH_local | exact GlobalTheory.CapelliLocality.capelliH_local | (intros; apply GlobalTheory.CapelliLocality.capelliH_local <;> assumption)
