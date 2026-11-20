import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.ContDiffConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.EpowMulOfKill
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.AdjointInv

namespace PositivityTheory.RgBcC

/- English proof (translation)
The claim follows from `Cxe.fr0Laws_of hR hG hM hD`.
-/
theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := Cxe.fr0Laws_of hR hG hM hD

/- English proof (translation)
The claim follows from `Cxe.swapLaws_of hR`.
-/
theorem swapLaws_of (hR : RmLaws) : SwapLaws := Cxe.swapLaws_of hR

/- English proof (translation)
The claim follows from `eigProd`.
-/
example : EigProd := eigProd
/- English proof (translation)
The claim follows from `avg_of`.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg := avg_of
/- English proof (translation)
The claim follows from `frOne'`.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrOne := frOne'
/- English proof (translation)
The claim follows from `frMulK'`.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrMulK := frMulK'
/- English proof (translation)
The claim follows from `frIso'`.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrIso := frIso'
/- English proof (translation)
The claim follows from `frCont'`.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrCont := frCont'

end PositivityTheory.RgBcC
