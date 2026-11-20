import Mathlib
import Formalism.PeriodIntegrals.ScalPairs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.BetaModXOfIota
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BetaModuloX.IotaSurjectiveHolds

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.BetaModX.betaModX_of_iota PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_surjective_holds D u u'`.
-/
theorem beta_mod_iota_surjective (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalPairs.BetaL D u u' :=
  PI.UnitaryGroupMassFormula.BetaModX.betaModX_of_iota PI.UnitaryGroupMassFormula.BetaModX.Iota.iota_surjective_holds D u u'
