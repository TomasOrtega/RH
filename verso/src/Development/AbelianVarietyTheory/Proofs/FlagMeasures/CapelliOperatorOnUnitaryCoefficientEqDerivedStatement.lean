import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CapelliCoef.capelli_coef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCapelliOperatorOnUnitaryCoefficientEqDerived.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived : PI.UnitaryGroupMassFormula.CapelliEig.FunAct := by
  first | exact @GlobalTheory.CapelliCoef.capelli_coef | exact GlobalTheory.CapelliCoef.capelli_coef | (intros; apply GlobalTheory.CapelliCoef.capelli_coef <;> assumption)
