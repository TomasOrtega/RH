import Mathlib
import Formalism.PeriodIntegrals.UnimodLocStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsIsometryMemLocalizedAtSingle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepAll

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.UnimodLocStd.target_of_key (PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_ram (PI.UnitaryGroupMassFormula.UnimodLocStd.keyStartRam_of_unit PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam))`.
-/
theorem unimodular_local_standard : PI.UnimodLocStd :=
  PI.UnitaryGroupMassFormula.UnimodLocStd.target_of_key
    (PI.UnitaryGroupMassFormula.UnimodLocStd.keyRep_of_ram
      (PI.UnitaryGroupMassFormula.UnimodLocStd.keyStartRam_of_unit PI.UnitaryGroupMassFormula.UnimodLocStd.unitVecRam))
