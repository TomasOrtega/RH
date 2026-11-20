import Mathlib
import Formalism.PeriodIntegrals.WeilQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.InvInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq

namespace PI

/- English proof (translation)
The claim follows from `PI.WeilQuotMeas.UnitaryGroupMassFormula.weilQuotient_of_parts PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat PI.WeilQuotMeas.UnitaryGroupMassFormula.stepInvInv PI.wqUnique`.
-/
theorem weil_quotient_measure : PI.WeilQuotMeas.WeilQuotient :=
  PI.WeilQuotMeas.UnitaryGroupMassFormula.weilQuotient_of_parts PI.WeilQuotMeas.UnitaryGroupMassFormula.stepBruhat
    PI.WeilQuotMeas.UnitaryGroupMassFormula.stepInvInv PI.wqUnique

end PI
