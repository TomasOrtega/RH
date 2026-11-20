import Mathlib
import Formalism.PeriodIntegrals.VacEntire
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.VacuumEntire.AnalyticAtHfLeft

/- English proof (translation)
Assemble the required witnesses or components as `⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩`.
-/
theorem entireStatements_holds : PI.VacEntire.Target :=
  ⟨PI.VacEntire.UnitaryGroupMassFormula.iopEntire, PI.VacEntire.UnitaryGroupMassFormula.tensEntire⟩
