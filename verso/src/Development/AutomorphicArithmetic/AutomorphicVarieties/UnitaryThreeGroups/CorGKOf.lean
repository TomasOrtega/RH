import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OneCharOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.OrbEquiv
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CountI

namespace UpperTheory.V.U3

/- English proof (translation)
The claim follows from `corGK (propGK h.number (oneChar h ha))`.
-/
theorem corGK_of (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : CorGK := corGK (propGK h.number (oneChar h ha))

/- English proof (translation)
The claim follows from `countI (corGK_of h ha)`.
-/
theorem caseI (h : Inp) (ha : Aut.AutomorphyUnramifiedCoefficients) : HV.CountI := countI (corGK_of h ha)

end UpperTheory.V.U3
