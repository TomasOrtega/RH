import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.FormalGroupLawExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdditiveIntegralGroups.GlueHoldsVar

namespace PI.AddIntG.Wk

/- English proof (translation)
The claim follows from `glue_holds_var formalGroupLawExists`.
-/
theorem addIntG_top : PI.AddIntG.Target := glue_holds_var formalGroupLawExists

end PI.AddIntG.Wk
