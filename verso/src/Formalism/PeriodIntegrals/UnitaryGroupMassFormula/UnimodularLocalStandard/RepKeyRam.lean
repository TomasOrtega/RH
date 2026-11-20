import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepKey
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem keyStart_of_keyStartRam (hR : KeyStartRam) : KeyStart := keyStart_of_ram hR

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem keyRep_of_ram (hR : KeyStartRam) : KeyRep := keyRep_of_start (keyStart_of_keyStartRam hR)

end PI.UnitaryGroupMassFormula.UnimodLocStd
