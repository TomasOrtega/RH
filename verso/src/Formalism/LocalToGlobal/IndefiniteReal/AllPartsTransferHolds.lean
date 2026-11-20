import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferOfFacts
import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
import Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
import Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing

namespace Formalism.IndefR.LatticeTransfer

/- English proof (translation)
The claim follows from `dimSq_of schur`.
-/
theorem dimSq : DimSq := dimSq_of schur

/- English proof (translation)
The claim follows from `idemP_of charFacts`.
-/
theorem idemP : IdemP := idemP_of charFacts

/- English proof (translation)
The claim follows from `core_of charFacts keyZero schur idemP`.
-/
theorem core : Core := core_of charFacts keyZero schur idemP

/- English proof (translation)
The claim follows from `all_parts_transfer_of_facts idemE idemP core dimSq metric`.
-/
theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
