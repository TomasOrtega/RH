import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOfCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerLinOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CntBasicOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowIntOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColSqOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowsColumnsSquareIntegrable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralWeightedSqLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralEnormRpowTwoNeTop
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchurOpOfSchurL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableReflect
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerMulOfKerBasicOfCvTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerEqIntegralConjMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompKey
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellSumOfCntBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoUnif
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvAdjEqAvg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KerClose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecCloseOfKerBasicColSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecNormOfVecClose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAtOfSqBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecInnerOfKerBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecLimOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall

namespace PositivityTheory.Rg.BcB.E1

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelBasic.kerBasic`.
-/
theorem kerBasic : KerBasic := GlobalTheory.CompanionTheory.KernelBasic.kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic kerBasic`.
-/
theorem kerLin : KerLin := GlobalTheory.CompanionTheory.KerLinear.kerLin_of_kerBasic kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic kerBasic`.
-/
theorem cntBasic : CntBasic := GlobalTheory.CompanionTheory.KernelCount.cntBasic_of_kerBasic kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic kerBasic`.
-/
theorem rowInt : RowInt := GlobalTheory.CompanionTheory.KernelRows.rowInt_of_kerBasic kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic kerBasic`.
-/
theorem colSq : ColSq := GlobalTheory.CompanionTheory.KernelColumn.colSq_of_kerBasic kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable kerBasic cntBasic colSq`.
-/
theorem kernel_rows_columns_square_integrable : KernelL2RowsColumns := GlobalTheory.CompanionTheory.KerSquare.kernel_rows_columns_square_integrable kerBasic cntBasic colSq
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Schur.schurL`.
-/
theorem schurL : SchurL := GlobalTheory.CompanionTheory.Schur.schurL
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SchurKernel.schurInt_of_schurL schurL`.
-/
theorem schurInt : SchurInt := GlobalTheory.CompanionTheory.SchurKernel.schurInt_of_schurL schurL
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL schurL`.
-/
theorem schurOp : SchurOp := GlobalTheory.CompanionTheory.Schur.schurOp_of_schurL schurL
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.ConvTest.cvTest`.
-/
theorem cvTest : CvTest := GlobalTheory.CompanionTheory.ConvTest.cvTest
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest kerBasic cvTest`.
-/
theorem kerMul : KerMul := GlobalTheory.CompanionTheory.KernelComposition.kerMul_of_kerBasic_of_cvTest kerBasic cvTest
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.OpEx.opExA kerBasic rowInt schurOp`.
-/
theorem opExA : OpExA := GlobalTheory.CompanionTheory.OpEx.opExA kerBasic rowInt schurOp
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KerAdj.opAdj_of kerBasic rowInt schurInt opExA`.
-/
theorem opAdj : OpAdj := GlobalTheory.CompanionTheory.KerAdj.opAdj_of kerBasic rowInt schurInt opExA
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelOperators.opMul kerBasic kerLin rowInt kernel_rows_columns_square_integrable schurInt cvTest kerMul`.
-/
theorem opMul : OpMul := GlobalTheory.CompanionTheory.KernelOperators.opMul kerBasic kerLin rowInt kernel_rows_columns_square_integrable schurInt cvTest kerMul
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelColumns.colOp kerBasic cvTest kernel_rows_columns_square_integrable kerMul`.
-/
theorem colOp : ColOp := GlobalTheory.CompanionTheory.KernelColumns.colOp kerBasic cvTest kernel_rows_columns_square_integrable kerMul
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic cntBasic`.
-/
theorem cellSum : CellSum := GlobalTheory.CompanionTheory.CellSumProof.cellSum_of_cntBasic cntBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif`.
-/
theorem twoUnif : TwoUnif := GlobalTheory.CompanionTheory.TwoSidedUnif.twoUnif
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Bump.bumpEx`.
-/
theorem bumpEx : BumpEx := GlobalTheory.CompanionTheory.Bump.bumpEx
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.ApproxUnit.approxU cvTest twoUnif`.
-/
theorem approxU : ApproxU := GlobalTheory.CompanionTheory.ApproxUnit.approxU cvTest twoUnif
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelClose.kerClose`.
-/
theorem kerClose : KerClose := GlobalTheory.CompanionTheory.KernelClose.kerClose
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq kerBasic colSq`.
-/
theorem vecClose : VecClose := GlobalTheory.CompanionTheory.KernelColumns.vecClose_of_kerBasic_colSq kerBasic colSq
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose vecClose`.
-/
theorem vecNorm : VecNorm := GlobalTheory.CompanionTheory.KernelColumns.vecNorm_of_vecClose vecClose
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KerVec.vecEx cntBasic kernel_rows_columns_square_integrable twoUnif vecClose`.
-/
theorem vecEx : VecEx := GlobalTheory.CompanionTheory.KerVec.vecEx cntBasic kernel_rows_columns_square_integrable twoUnif vecClose
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic kerBasic`.
-/
theorem vecInner : VecInner := GlobalTheory.CompanionTheory.E1.vecInner_of_kerBasic kerBasic
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KernelColumns.vecLim_of cntBasic cvTest colOp approxU vecClose`.
-/
theorem vecLim : VecLim := GlobalTheory.CompanionTheory.KernelColumns.vecLim_of cntBasic cvTest colOp approxU vecClose
/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.KerPoint.ptEq_of kerBasic cvTest opAdj colOp bumpEx approxU kerClose vecLim`.
-/
theorem ptEq : PtEq := GlobalTheory.CompanionTheory.KerPoint.ptEq_of kerBasic cvTest opAdj colOp bumpEx approxU kerClose vecLim

end PositivityTheory.Rg.BcB.E1
