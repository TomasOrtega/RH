import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.HasDerivAtInvLine
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.AtTraceT
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.DeterminantRankOneUpdate.DetOneAddSingle

namespace PositivityTheory.RgBcC

/- English proof (translation)
The claim follows from `Cxd2.rmHol_of Cxd2.atTrace Cxd2.atDer`.
-/
theorem rmHol : RmHol := Cxd2.rmHol_of Cxd2.atTrace Cxd2.atDer

/- English proof (translation)
The claim follows from `Cxd2.rmAnti_of Cxd2.atTraceT Cxd2.atDer`.
-/
theorem rmAnti : RmAnti := Cxd2.rmAnti_of Cxd2.atTraceT Cxd2.atDer

end PositivityTheory.RgBcC
