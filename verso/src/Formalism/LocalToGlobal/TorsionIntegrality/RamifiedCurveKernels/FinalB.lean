import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.IntDThmBOf
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.IntDBG

namespace Formalism.L2.Th1.G

/- English proof (translation)
The claim follows from `IntDThmB_of intAtD shapeCong`.
-/
theorem intDThmB : IntDThmB := IntDThmB_of intAtD shapeCong
/- English proof (translation)
The claim follows from `IntDThmBGauss_of intAtD shapeCong`.
-/
theorem intDThmBGauss : IntDThmBGauss := IntDThmBGauss_of intAtD shapeCong

end Formalism.L2.Th1.G
