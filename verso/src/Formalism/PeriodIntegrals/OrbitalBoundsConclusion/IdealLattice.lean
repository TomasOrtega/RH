import Mathlib
import Formalism.PeriodIntegrals.IdealLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.OKArea
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasis

/- English proof (translation)
The claim follows from `PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis`.
-/
theorem ideal_lattice_basis : PI.IdealLattice :=
  PI.IdealLatticeWork.idealLattice_of PI.IdealLatticeWork.okArea PI.IdealLatticeWork.idealBasis
