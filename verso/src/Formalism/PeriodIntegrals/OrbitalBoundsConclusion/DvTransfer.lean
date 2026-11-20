import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DvTransferMain

/- English proof (translation)
The claim follows from `PI.Dv.Tr.dvTransfer_main`.
-/
theorem division_transfer_ranks : PI.Dv.Conclusion4a := PI.Dv.Tr.dvTransfer_main
