import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SzLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.LatSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThCont
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RatGl
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharInt
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DMOne
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbFn
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Rev

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
The claim follows from `maj latSum decE`.
-/
theorem maj_holds : Maj := maj latSum decE

/- English proof (translation)
The claim follows from `meanZero decE`.
-/
theorem meanZero_holds : MeanZero := meanZero decE

/- English proof (translation)
The claim follows from `f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)`.
-/
theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

/- English proof (translation)
The claim follows from `rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont) (coefPer decE maj_holds orbS momKill (orbFn orbS))`.
-/
theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent
