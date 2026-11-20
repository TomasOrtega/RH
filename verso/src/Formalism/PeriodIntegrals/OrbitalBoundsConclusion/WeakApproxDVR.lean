import Mathlib
import Formalism.PeriodIntegrals.WeakApproxDVR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.BigExistenceHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeakApproximationDVR.RhoProjectionAssembly

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weak_approximation_dvr : PI.WeakApproxDVR :=
  PI.WA.weakApproxDVR_of PI.WA.big_existence_holds PI.WA.rho_projection_assembly
