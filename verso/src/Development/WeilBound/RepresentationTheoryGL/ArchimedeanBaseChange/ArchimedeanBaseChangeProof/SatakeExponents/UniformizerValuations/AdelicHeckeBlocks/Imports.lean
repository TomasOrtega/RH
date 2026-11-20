import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsHeckeSmul
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.SelfAdj

namespace PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

open PositivityTheory.RgBcC

/- English proof (translation)
The claim follows from `blkOp' wave_existence_speed_multiplicity.2.2.2`.
-/
theorem blkOp₀ : BlockOperatorsProductAdjoint := blkOp' wave_existence_speed_multiplicity.2.2.2

/- English proof (translation)
The claim follows from `blkComm' wave_existence_speed_multiplicity.2.2.2`.
-/
theorem blkComm₀ : BlockPureTensorsCommute := blkComm' wave_existence_speed_multiplicity.2.2.2

/- English proof (translation)
The claim follows from `blkWord' wave_existence_speed_multiplicity.2.2.2`.
-/
theorem blkWord₀ : BlockWordOperators := blkWord' wave_existence_speed_multiplicity.2.2.2

/- English proof (translation)
The claim follows from `pTTest' wave_existence_speed_multiplicity.2.2.1`.
-/
theorem pTTest₀ : PTTest := pTTest' wave_existence_speed_multiplicity.2.2.1

/- English proof (translation)
The claim follows from `blkGrowth' wave_existence_speed_multiplicity.2.2.2 h`.
-/
theorem blkGrowth₀ (h : D4.EllFormula2J) : BlockEllipticGrowth := blkGrowth' wave_existence_speed_multiplicity.2.2.2 h

/- English proof (translation)
The claim follows from `locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3`.
-/
theorem locOk₀ : LocOk := locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

/- English proof (translation)
The claim follows from `locComm idemAlg sphComm PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3`.
-/
theorem locComm₀ : LocComm := locComm idemAlg sphComm PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

/- English proof (translation)
The claim follows from `seenTr PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3`.
-/
theorem seenTr₀ : SeenTr := seenTr PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

/- English proof (translation)
The claim follows from `sqOk adjKer₀ blkOp₀ blkWord₀`.
-/
theorem sqOk₀ : SqOk := sqOk adjKer₀ blkOp₀ blkWord₀

end PositivityTheory.Rg.BcB.F.BlockFiniteConvolution
