import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCountPfFinal

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds`.
-/
theorem ooLintSumC_outright : OOLintSumC :=
  ooLintSumC_holds_slab Formalism.L2.SG.Pf.SlabMajPt.pointwise_majorant_by_columns Formalism.L2.SG.Pf.SlabCount.countC_holds

/- English proof (translation)
The claim follows from `absConvC_holds_of ooLintSumC_outright`.
-/
theorem absConvC_outright : Formalism.L2.SG.Full.AbsConvC := absConvC_holds_of ooLintSumC_outright

end Formalism.L2.SG.Pf
