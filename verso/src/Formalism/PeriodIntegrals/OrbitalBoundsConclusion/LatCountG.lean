import Mathlib
import Formalism.PeriodIntegrals.LatCountG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_count_all : PI.LatCountG.LatCountAll :=
  PI.UnitaryGroupMassFormula.LCG.latCountAll_of_idx PI.UnitaryGroupMassFormula.LCG.determinant_index_formula PI.UnitaryGroupMassFormula.LCG.lattice_indexOf
