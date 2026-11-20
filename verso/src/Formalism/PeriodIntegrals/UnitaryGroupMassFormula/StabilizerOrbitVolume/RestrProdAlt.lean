import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RestrProdG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FiniteOnCompacts
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RPGlue
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.RpAbsHolds

namespace PI.VolStabSW

/- English proof (translation)
The claim follows from `restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds RestrProdA.rpTail_holds RestrProdA.latCofin_holds`.
-/
theorem restrProd_holds : RestrProd :=
  restrProd_of rpAbs_holds rpFib_holds rpGlue_holds RestrProdG.rpGram_holds
    RestrProdA.rpTail_holds RestrProdA.latCofin_holds

end PI.VolStabSW
