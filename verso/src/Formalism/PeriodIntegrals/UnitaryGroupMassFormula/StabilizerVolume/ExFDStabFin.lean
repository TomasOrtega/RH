import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExFDStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.EqZeroOfMemNbhdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.LocallyCompactAdelicUnitary

namespace PI.VolStabS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discHF_holds : DiscHF :=
  discHF_of_discHA (PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exFDStab_holds : ExFDStab := exFDStab_of scha_holds discHF_holds

end PI.VolStabS
