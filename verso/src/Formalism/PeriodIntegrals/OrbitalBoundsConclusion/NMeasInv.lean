import Mathlib
import Formalism.PeriodIntegrals.NMeasInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.MeasureContractionFormula

namespace PI

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem n_measure_invariant : PI.NMeasInv.Target :=
  PI.NMeasInv.UnitaryGroupMassFormula.nMeasInv_of PI.NMeasInv.UnitaryGroupMassFormula.measure_contraction_formula

end PI
