import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.ContDiffConjTranspose
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.EpowMulOfKill
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.AdjointInv

namespace PositivityTheory.RgBcC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := Cxe.fr0Laws_of hR hG hM hD

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem swapLaws_of (hR : RmLaws) : SwapLaws := Cxe.swapLaws_of hR

/- English proof (translation)
A detailed English derivation is pending.
-/
example : EigProd := eigProd
/- English proof (translation)
A detailed English derivation is pending.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg := avg_of
/- English proof (translation)
A detailed English derivation is pending.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrOne := frOne'
/- English proof (translation)
A detailed English derivation is pending.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrMulK := frMulK'
/- English proof (translation)
A detailed English derivation is pending.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrIso := frIso'
/- English proof (translation)
A detailed English derivation is pending.
-/
example : MatrixFrechetDerivativeAtZeroLaws → Avg → FrCont := frCont'

end PositivityTheory.RgBcC
