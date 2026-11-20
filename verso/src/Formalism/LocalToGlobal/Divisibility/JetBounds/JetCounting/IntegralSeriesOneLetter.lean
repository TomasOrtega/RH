import Formalism.LocalToGlobal.Divisibility.Numbers
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.JetCountingProofs.SerAlongComp
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetCounting.JetCountingProofs.IntegralCombinationHolds

namespace Formalism.L2.DIV.C

/- English proof (translation)
The claim follows from `integralFree_holds`.
-/
theorem hostIntFree : HostIntFree := integralFree_holds

end Formalism.L2.DIV.C
