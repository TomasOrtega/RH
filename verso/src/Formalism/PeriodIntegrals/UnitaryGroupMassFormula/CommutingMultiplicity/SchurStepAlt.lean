import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurIrreducible

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep`.
-/
theorem schurStep : SchurStep :=
  _root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep

end PI.UnitaryGroupMassFormula.CommMult
