import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CommutingMultiplicity.SchurStep
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchurIrreducible

namespace PI.UnitaryGroupMassFormula.CommMult

open Matrix

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem schurStep : SchurStep :=
  _root_.UpperTheory.Reformulated.B.SchurIrreducible.schurStep

end PI.UnitaryGroupMassFormula.CommMult
