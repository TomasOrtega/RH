import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayDensEx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.CayValId

namespace PI.AprimeInfW

/- English proof (translation)
The claim follows from `expProdU_of_hua cayDensEx_holds cayValId_holds`.
-/
theorem expProdU_holds : ExpProdU := expProdU_of_hua cayDensEx_holds cayValId_holds

end PI.AprimeInfW
