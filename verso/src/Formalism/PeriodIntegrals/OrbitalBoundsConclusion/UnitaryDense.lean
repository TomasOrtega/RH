import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.VanishInvertible
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Decomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.Derived

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem productFramesDense_holds : PI.FramesDense := PI.UD.framesDense_of PI.UD.svdStep PI.UD.gramStep

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitaryGroupDense_holds : PI.UnitaryDense := unitaryDense_of productFramesDense_holds
