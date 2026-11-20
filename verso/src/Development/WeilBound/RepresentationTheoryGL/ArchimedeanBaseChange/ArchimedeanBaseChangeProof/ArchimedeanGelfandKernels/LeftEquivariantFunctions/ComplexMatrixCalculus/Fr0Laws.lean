import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.FrMulK
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.SwapLawsOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.DeterminantPowerSmoothness.GtCharZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.ToLinSmulOne
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.DerTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ConjugateTransposeDerivatives.HasDerivAtConjTranspose

namespace PositivityTheory.RgBcC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fr0Laws : MatrixFrechetDerivativeAtZeroLaws := fr0Laws_of rmLaws gamMul mtLaws gamDer

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem avg : Avg := avg_of fr0Laws

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frOne : FrOne := frOne' fr0Laws avg
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frMulK : FrMulK := frMulK' fr0Laws avg
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frIso : FrIso := frIso' fr0Laws avg
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frCont : FrCont := frCont' fr0Laws avg

end PositivityTheory.RgBcC
