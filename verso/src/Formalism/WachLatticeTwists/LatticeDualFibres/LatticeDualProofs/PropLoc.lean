import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.LocDualOrth
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.QuotLen

universe u

namespace Formalism.RepresentationBoundsCohomology.LOC

/- English proof (translation)
The claim follows from `propLoc_of locQuotLen`.
-/
theorem propLoc : StatPropLoc.{u} := propLoc_of locQuotLen

end Formalism.RepresentationBoundsCohomology.LOC
