import Mathlib
import Formalism.PeriodIntegrals.AutLzFinite
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.AutLzFinMain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem automorphism_lattice_finite (D : Formalism.BasicNotions.D7) : PI.AutLzFinite.AutLzFin D :=
  PI.AutLzFinite.SlopeTestRemainingChoices.autLzFin_main D
