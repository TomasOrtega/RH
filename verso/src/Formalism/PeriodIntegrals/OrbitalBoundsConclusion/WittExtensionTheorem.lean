import Mathlib
import Formalism.PeriodIntegrals.WittExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.OneVector
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.AnisotropicHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WittDecomposition.WittOf

/- English proof (translation)
The claim follows from `PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'`.
-/
theorem witt_extension_theorem : PI.WittExtension :=
  PI.Witt.witt_of PI.Witt.one_vector_holds PI.Witt.anisotropic'
