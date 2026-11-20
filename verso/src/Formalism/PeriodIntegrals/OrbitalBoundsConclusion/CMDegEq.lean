import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CMDegreeEquality.FinrankEqTwo

/- English proof (translation)
The claim follows from `CMDeg.degEq`.
-/
theorem Formalism.L2.SG.MassRatio.cm_degree_eq : Formalism.L2.SG.MassRatio.DegEq := CMDeg.degEq
