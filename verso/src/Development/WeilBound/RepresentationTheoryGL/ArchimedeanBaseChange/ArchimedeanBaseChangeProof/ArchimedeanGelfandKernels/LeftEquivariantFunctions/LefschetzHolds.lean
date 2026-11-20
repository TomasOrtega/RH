import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.LefOfKChain
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.KChainHolds

namespace PositivityTheory.RgBcC

/- English proof (translation)
The claim follows from `lef_of_kChain LfSt.kChain_holds`.
-/
theorem lefschetz_holds : Lef := lef_of_kChain LfSt.kChain_holds

end PositivityTheory.RgBcC
