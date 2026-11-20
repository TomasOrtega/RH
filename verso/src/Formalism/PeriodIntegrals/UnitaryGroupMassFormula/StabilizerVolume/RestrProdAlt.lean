import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FiniteOnCompacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RpAbsHolds

namespace PI.VolStabS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabS
