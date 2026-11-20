import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.HSBlocksMain

/- English proof (translation)
The claim follows from `NormHilbertSchmidtBlocks.hSBlocks_main`.
-/
theorem hilbert_schmidt_blocks : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
