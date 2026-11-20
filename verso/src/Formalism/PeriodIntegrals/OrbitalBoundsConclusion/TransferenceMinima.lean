import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Skeleton
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.Poisson
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.NumericMain
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.KeySmall

/- English proof (translation)
The claim follows from `PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall`.
-/
theorem transference_successive_minima : PI.TransferenceMinima :=
  PI.Tr.transferenceMinima_of' PI.Tr.poissonGauss PI.Tr.gaussStep PI.Tr.keySmall
