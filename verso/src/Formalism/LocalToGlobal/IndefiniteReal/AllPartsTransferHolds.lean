import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferOfFacts
import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
import Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
import Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing

namespace Formalism.IndefR.LatticeTransfer

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dimSq : DimSq := dimSq_of schur

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idemP : IdemP := idemP_of charFacts

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem core : Core := core_of charFacts keyZero schur idemP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
