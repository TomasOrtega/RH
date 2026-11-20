import Mathlib
import Formalism.PeriodIntegrals.BeConjNorm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.BeConjNormOfIntInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateNormBound.MemIntegerRingIffNormLeOne

/- English proof (translation)
The claim follows from `PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic`.
-/
theorem conjugate_norm_bound : PI.BeConjNorm.BeConjNorm :=
  PI.BeConjNormW.beConjNorm_of_intInv PI.BeConjNormW.inverse_integral_padic
