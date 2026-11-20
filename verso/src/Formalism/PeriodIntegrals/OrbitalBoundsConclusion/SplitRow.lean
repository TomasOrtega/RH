import Mathlib
import Formalism.PeriodIntegrals.SplitRow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.MeasureIsomorphismAtInfinity

/- English proof (translation)
The claim follows from `PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity`.
-/
theorem split_row_iso : PI.SplitRow.SplitRow := PI.SRW.splitRow_of_iso PI.SRW.measure_isomorphism_at_infinity
