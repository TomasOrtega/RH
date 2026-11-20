import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.ClassVanishOfSteps
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.QuotVanishL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImgEqOfInvariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AevalTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogSizeNonneg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwConjCentMul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EnormOfRealToRealLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralProdSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCornerGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetOneAddOfSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceFiniteAdeleRingCmField
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.IsCompactEntryBall
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSdot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralNonnegNormaliserEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.T2SpaceAdelicGLCmField

namespace PositivityTheory.Rg.BcB.CV

open PositivityTheory.Rg.BcB.D1 GlobalTheory.CompanionTheory

/- English proof (translation)
The claim follows from `classVanish_of_steps QuotNorm.integral_normaliser_eq (QuotProduct.quotProd_of_normEq QuotNorm.integral_normaliser_eq) chainSum RatDisc.ratDisc locVanish LocP.main LocFlagPf.locFlag degBdd KerTwFin.kerFin mahler SplitInf.splitAt NonEll.nonEllFlag SplitTwo.splitAt2 PairParam.pairPa …`.
-/
theorem classVanish : ClassVanish :=
  classVanish_of_steps QuotNorm.integral_normaliser_eq (QuotProduct.quotProd_of_normEq QuotNorm.integral_normaliser_eq) chainSum
    RatDisc.ratDisc locVanish LocP.main LocFlagPf.locFlag degBdd KerTwFin.kerFin mahler SplitInf.splitAt NonEll.nonEllFlag
    SplitTwo.splitAt2 PairParam.pairParam (TorusCh.torusChar degAdelic)
    (ChiGamGlobal.chiGam_of onlyIsotropic (PosYGlobal.posY_of degSubmod degPairing) chainSum)
    (QuotStageInt.quotStage_of QuotNorm.integral_normaliser_eq) sizeBasic

/- English proof (translation)
The claim follows from `UnfoldCut.unfold_of_mahler mahler`.
-/
theorem unfold : Unfold := UnfoldCut.unfold_of_mahler mahler

/- English proof (translation)
The claim follows from `ellFormula_of unfold ellTerm classVanish sizeBasic`.
-/
theorem ellFormula : EllFormula := ellFormula_of unfold ellTerm classVanish sizeBasic

end PositivityTheory.Rg.BcB.CV
