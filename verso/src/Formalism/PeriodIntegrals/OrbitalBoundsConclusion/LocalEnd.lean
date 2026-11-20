import Mathlib
import Formalism.PeriodIntegrals.LocalEnd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.HenselRoot
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalEndomorphisms.IntVal

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_endomorphism_homeomorph : PI.LocalEndHomeo :=
  PI.LocalEndW.localEndHomeo_of_three PI.LocalEndW.henselRoot PI.LocalEndW.intOfHensel PI.LocalEndW.valOfInt
