import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.HasCompactSupportOfSection
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntryLeOfLg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.LogSizeInv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ConvTest
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.AdelRep
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.NrmLCharpoly
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.AdjKer0

namespace PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

open PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.D1

/- English proof (translation)
The claim follows from `finConv intHint hintProd slots`.
-/
theorem finConv' : FinConv := finConv intHint hintProd slots

/- English proof (translation)
The claim follows from `fmAlg finConv' slots`.
-/
theorem fmAlg' : FmAlg := fmAlg finConv' slots

/- English proof (translation)
The claim follows from `fmTr slots`.
-/
theorem fmTr' : FmTr := fmTr slots

/- English proof (translation)
The claim follows from `rtAlg sizeBasic`.
-/
theorem rtAlg' : RtAlg := rtAlg sizeBasic

/- English proof (translation)
The claim follows from `adelRep fmAlg' fmTr' rtAlg'`.
-/
theorem adelRep' : AdelRep := adelRep fmAlg' fmTr' rtAlg'

/- English proof (translation)
The claim follows from `blkOp E1.opEx_holds h tensTest tensMul`.
-/
theorem blkOp' (h : MultAlg) : BlockOperatorsProductAdjoint := blkOp E1.opEx_holds h tensTest tensMul

/- English proof (translation)
The claim follows from `blkComm E1.opEx_holds h tensTest tensMul`.
-/
theorem blkComm' (h : MultAlg) : BlockPureTensorsCommute := blkComm E1.opEx_holds h tensTest tensMul

/- English proof (translation)
The claim follows from `blkWord (blkOp' h)`.
-/
theorem blkWord' (h : MultAlg) : BlockWordOperators := blkWord (blkOp' h)

/- English proof (translation)
The claim follows from `pTTest regOf finConv' fmTr' h`.
-/
theorem pTTest' (h : KerEx) : PTTest := pTTest regOf finConv' fmTr' h

/- English proof (translation)
The claim follows from `blkGrowth (blkOp' h) (blkWord' h) blkSum (ellLin h')`.
-/
theorem blkGrowth' (h : MultAlg) (h' : D4.EllFormula2J) : BlockEllipticGrowth := blkGrowth (blkOp' h) (blkWord' h) blkSum (ellLin h')

end PositivityTheory.Rg.BcB.F.BlockFiniteConvolution
