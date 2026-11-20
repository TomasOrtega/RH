import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirabolicBound.MirabolicBound

/- English proof (translation)
The claim follows from `PI.GGMirBoundW.mirabolicBound`.
-/
theorem mirabolic_bound : Formalism.L2.SG.GGMirabolic.MirabolicBound :=
  PI.GGMirBoundW.mirabolicBound
