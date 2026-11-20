import Mathlib
import Formalism.PeriodIntegrals.KerIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.KerLocIsoOfNormOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOne

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernel_local_iso : PI.KerIso.LocIso := PI.KLW.kerLocIso_of_normOne PI.KLW.normOne
