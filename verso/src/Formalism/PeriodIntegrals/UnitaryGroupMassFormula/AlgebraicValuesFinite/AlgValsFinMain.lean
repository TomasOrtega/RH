import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinOfTors
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.TorsUnitsOfNbhd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.InvMemUFin

noncomputable section

namespace PI.AlgValsFin.W

/- English proof (translation)
The claim follows from `torsUnits_of_nbhd L fun W hW h1 => exists_nbhd W hW h1`.
-/
theorem torsUnits (L : Type) [Field L] [NumberField L] : TorsUnits L :=
  torsUnits_of_nbhd L fun W hW h1 => exists_nbhd W hW h1

/- English proof (translation)
The claim follows from `algValsFin_of_tors L (torsUnits L)`.
-/
theorem algValsFin_main (L : Type) [Field L] [NumberField L] : AlgValsFin L :=
  algValsFin_of_tors L (torsUnits L)

end PI.AlgValsFin.W
