import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyExact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.KeyNewton

namespace PI.UnitaryGroupMassFormula.UnimodLocStd

/- English proof (translation)
The claim follows from `keyRep_of hS keyNewton keyExact`.
-/
theorem keyRep_of_start (hS : KeyStart) : KeyRep := keyRep_of hS keyNewton keyExact

end PI.UnitaryGroupMassFormula.UnimodLocStd
