import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalC
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveJetsUnramifiedHolds

namespace Formalism.L2.Th1.G

/- English proof (translation)
The claim follows from `integral_unramified_holds`.
-/
theorem intUnram : IntUnram := integral_unramified_holds
/- English proof (translation)
The claim follows from `curve_jets_unramified_holds`.
-/
theorem curveJetsUnramThm : CurveJetsUnram := curve_jets_unramified_holds

end Formalism.L2.Th1.G
