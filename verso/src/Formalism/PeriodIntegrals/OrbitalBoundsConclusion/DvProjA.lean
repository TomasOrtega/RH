import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvIdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LengthIndex.IdxEqLen

/- English proof (translation)
The claim follows from `dvProjA_of division_index_calc`.
-/
theorem projection_sandwich : PI.Dv.ProjA := dvProjA_of division_index_calc
