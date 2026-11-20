import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKey
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

/- English proof (translation)
The claim follows from `keyStart_of_ram hR`.
-/
theorem keyStart_of_keyStartRam (hR : KeyStartRam) : KeyStart := keyStart_of_ram hR

/- English proof (translation)
The claim follows from `keyRep_of_start (keyStart_of_keyStartRam hR)`.
-/
theorem keyRep_of_ram (hR : KeyStartRam) : KeyRep := keyRep_of_start (keyStart_of_keyStartRam hR)

end PI.UnitaryGroupMassFormula.UnimodLocStd
