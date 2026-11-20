import Mathlib
import Formalism.LocalToGlobal.AdelicCompactOpens.HermDefONFamily
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianDefiniteOrthonormal.Imports

/- English proof (translation)
Introduce `_ G hG` and use `PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG`.
-/
theorem posDefCongruentOne : Formalism.L2.Props.HermDefON := fun _ G hG => PI.UnitaryGroupMassFormula.HermDefON.exists_congr_one G hG
