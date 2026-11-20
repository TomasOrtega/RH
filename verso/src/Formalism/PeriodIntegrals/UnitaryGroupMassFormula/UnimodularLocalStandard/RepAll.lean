import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKeyRam
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepRamAsm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.UnitVecRam

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

/- English proof (translation)
The claim follows from `keyRep_of_ram (keyStartRam_of_unit unitVecRam)`.
-/
theorem keyRep : KeyRep := keyRep_of_ram (keyStartRam_of_unit unitVecRam)

end PI.UnitaryGroupMassFormula.UnimodLocStd
