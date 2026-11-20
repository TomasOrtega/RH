import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds

namespace PI.AprimeInfW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expProdU_of_G (h : CayDensG) : ExpProdU := expProdU_of_cayProdU (cayProdU_of_G h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expProdU_of_hua (h1 : CayDensEx) (h2 : CayValId) : ExpProdU := expProdU_of_G (cayDensG_of h1 h2)

end PI.AprimeInfW
