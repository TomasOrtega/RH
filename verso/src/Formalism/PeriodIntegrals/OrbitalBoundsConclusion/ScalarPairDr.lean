import Mathlib
import Formalism.PeriodIntegrals.ScalarPairDr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ScalarPairOrthogonal.ExistsNeZeroMem

/- English proof (translation)
The claim follows from `PI.ScalarPairDr.W.scalarDr D u u'`.
-/
theorem scalar_pair_dr (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) : PI.ScalarPairDr.ScalarDr D u u' :=
  PI.ScalarPairDr.W.scalarDr D u u'
