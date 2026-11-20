import Formalism.PeriodIntegrals.HermLatFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianLatticeFiniteness.HermLatFinMain

/- English proof (translation)
The claim follows from `PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main`.
-/
theorem hermitian_lattice_finite : PI.HermLatFin.HermLatFin :=
  PI.HermLatFin.UnitaryGroupMassFormula.hermLatFin_main
