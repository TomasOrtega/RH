import Mathlib
import Formalism.PeriodIntegrals.SelfDualLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.SelfDualLocOfLocBasis
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SelfDualLocalBasis.LocBasis

/- English proof (translation)
The claim follows from `PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis`.
-/
theorem self_dual_local : PI.SelfDualLoc :=
  PI.SelfDualLoc.W.selfDualLoc_of_locBasis PI.SelfDualLoc.W.locBasis
