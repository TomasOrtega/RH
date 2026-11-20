import Mathlib
import Formalism.PeriodIntegrals.Minkowski
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.CharpolyDvdOfPowEqOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSum
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.MinkowskiBoundOfSteps

/- English proof (translation)
The claim follows from `PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep`.
-/
theorem card_dvd_minkowskiNumber : PI.MinkowskiBound :=
  PI.Mk.minkowskiBound_of_steps PI.Mk.traceStep PI.Mk.powerSumStep
