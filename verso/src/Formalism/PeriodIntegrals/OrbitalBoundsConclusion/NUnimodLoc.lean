import Formalism.PeriodIntegrals.NUnimodLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.FrameC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnimodularLattice.Transf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem n_unimodular_local : PI.NUnimodLoc.NUnimodLoc :=
  PI.NUnimodLoc.UnitaryGroupMassFormula.nUnimodLoc_of PI.NUnimodLoc.UnitaryGroupMassFormula.FC.frame_conjugation_unimodular
    PI.NUnimodLoc.UnitaryGroupMassFormula.TR.transfer_holds
