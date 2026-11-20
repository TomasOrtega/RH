import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.BlockValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoinvReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Expand
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsComb
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.InhabitantsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Inhabitants
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Lattice
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterAtIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCharacterBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTopGeneral
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAboveTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvariantTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTopGeneral
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvAtTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvIdealRepresentation
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvMonomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvPolynomialReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStaircaseDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCoinvStepReduction
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCardYoungCells
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordInj
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCellOfWordMono
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfAtStair
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfMonomialPsumOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfUpdateZero
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombCfVandermondePsumOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombDetDescFactorial
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombExtendWord
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookBranch
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombHookShapeFacts
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombPcntAppend
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortLe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShiftDistinct
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombSortShift
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombStripSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauOfWord
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowLattice
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombTableauRowPrefix
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombVandermondeSucc
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombWordOfTableau
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PCombYoungRowCard
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltCoeffInjective
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAltTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymDecomposition
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagAntisymHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagCoeffBlockPermute
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffNotDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDiffPrime
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagDividedDifferencePoly
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagHomogeneousComponentMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagInjSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralAntisymmetrize
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralKillsPowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralPermute
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralTopDegree
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondeMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralVandermondePos
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagIntegralViaQuotient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagPowerSumPreimage
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagPowerSumSymmetric
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagProdPrimesDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagQuotientHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictConstantCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictDecomposition
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictPowerSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagRestrictSymmetric
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagStaircaseOrbit
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSwapDivisible
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagSymmetricMulAntisym
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeDvd
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFlagVandermondeHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusCharacterFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PFrobeniusDimensionFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookCharacterSumIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookDimensionSum
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHookTableauCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PIntegralIsDividedDifference
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaA
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaB
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLemmaC
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PLinearTermValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Pluecker
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.POtherFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PowerSums
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTablePos
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestBoundOfPrimeBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestInnerTsumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestKSumBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialDecomposes
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneousDecomposition
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPolynomialHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestPrimeBoundOfFactor
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PRestTermWellDefined
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorBound
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSameFactorFormula
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAevalSignedRename
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAlternantRenamePlace
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAltPartitionExpansion
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchAntisymmetrizePlace
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchBlockVandermondeOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchCompleteGenerating
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternant
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatAlternantZero
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchConcatExponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchEvalPowerSumHom
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchHookResidues
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchJTMatrixDetAtRoots
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchNonHookResidues
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchPowerSumHomWeighted
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchProdOneSubRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchResidueCount
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityBialternant
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsEq
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityRowsPerm
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchRootOfUnityVandermondeNe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurAtRootsOfUnity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurEvalMatrix
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSchurRowsToK
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchSmallBlockProduct
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchStrictAntiSplit
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurPowerSumCoefficient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchurSignCoefficient
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PSchWeightedPreimage
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PShiftSumRule
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PTotalIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PVandermondeOfHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PrimeWeightEqZeroOfLt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableTranspose
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.SameFactorDegreeClauseOfValue
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AntisymmetrizeBlockVandermondeOf
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StaircaseIsHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.TenNinthsLe
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.NumStandardTableEqCardMonotone
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.CoeffRenameProdCongrRight
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.VandermondeEqVandermondeOf
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.RestAt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.DegPolynomialIsHomogeneous
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealTransferOfSyzygy
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.OfHookCharacterSumIdentity
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealRootRingToRealAlt
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.SumPderivRealApply
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

/- English proof (translation)
The claim follows from `CoinvStepReduction.proof`.
-/
theorem CoinvStepReduction.full : CoinvStepReduction.Statement :=
  CoinvStepReduction.proof

/- English proof (translation)
The claim follows from `CoinvMonomialReduction.proof CoinvStepReduction.full`.
-/
theorem CoinvMonomialReduction.full : CoinvMonomialReduction.Statement :=
  CoinvMonomialReduction.proof CoinvStepReduction.full

/- English proof (translation)
The claim follows from `CoinvPolynomialReduction.proof CoinvMonomialReduction.full`.
-/
theorem CoinvPolynomialReduction.full : CoinvPolynomialReduction.Statement :=
  CoinvPolynomialReduction.proof CoinvMonomialReduction.full

/- English proof (translation)
The claim follows from `CoinvIdealRepresentation.proof`.
-/
theorem CoinvIdealRepresentation.full : CoinvIdealRepresentation.Statement :=
  CoinvIdealRepresentation.proof

/- English proof (translation)
The claim follows from `HomogeneousComponentMul.proof`.
-/
theorem HomogeneousComponentMul.full : HomogeneousComponentMul.Statement :=
  HomogeneousComponentMul.proof

/- English proof (translation)
The claim follows from `CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full`.
-/
theorem CoinvIdealComponent.full : CoinvIdealComponent.Statement :=
  CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full

/- English proof (translation)
The claim follows from `CoinvStaircaseDegree.proof`.
-/
theorem CoinvStaircaseDegree.full : CoinvStaircaseDegree.Statement :=
  CoinvStaircaseDegree.proof

/- English proof (translation)
The claim follows from `CoinvStaircaseComponent.proof CoinvStaircaseDegree.full`.
-/
theorem CoinvStaircaseComponent.full : CoinvStaircaseComponent.Statement :=
  CoinvStaircaseComponent.proof CoinvStaircaseDegree.full

/- English proof (translation)
The claim follows from `CoinvAtTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full`.
-/
theorem CoinvAtTop.full : CoinvAtTop.Statement :=
  CoinvAtTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

/- English proof (translation)
The claim follows from `CoinvariantTopDegree.proof CoinvAtTop.full`.
-/
theorem CoinvariantTopDegree.full : CoinvariantTopDegree.Statement :=
  CoinvariantTopDegree.proof CoinvAtTop.full

/- English proof (translation)
The claim follows from `FlagCoeffBlockPermute.proof`.
-/
theorem FlagCoeffBlockPermute.full : FlagCoeffBlockPermute.Statement :=
  FlagCoeffBlockPermute.proof

/- English proof (translation)
The claim follows from `FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full`.
-/
theorem FlagAltCoeffInjective.full : FlagAltCoeffInjective.Statement :=
  FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full

/- English proof (translation)
The claim follows from `FlagInjSumBound.proof`.
-/
theorem FlagInjSumBound.full : FlagInjSumBound.Statement :=
  FlagInjSumBound.proof

/- English proof (translation)
The claim follows from `FlagStaircaseOrbit.proof`.
-/
theorem FlagStaircaseOrbit.full : FlagStaircaseOrbit.Statement :=
  FlagStaircaseOrbit.proof

/- English proof (translation)
The claim follows from `FlagVandermondeHomogeneous.proof`.
-/
theorem FlagVandermondeHomogeneous.full : FlagVandermondeHomogeneous.Statement :=
  FlagVandermondeHomogeneous.proof

/- English proof (translation)
The claim follows from `FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full`.
-/
theorem FlagAltTopDegree.full : FlagAltTopDegree.Statement :=
  FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full

/- English proof (translation)
The claim follows from `FlagAntisymHomogeneous.proof`.
-/
theorem FlagAntisymHomogeneous.full : FlagAntisymHomogeneous.Statement :=
  FlagAntisymHomogeneous.proof

/- English proof (translation)
The claim follows from `FlagIntegralPermute.proof FlagCoeffBlockPermute.full`.
-/
theorem FlagIntegralPermute.full : FlagIntegralPermute.Statement :=
  FlagIntegralPermute.proof FlagCoeffBlockPermute.full

/- English proof (translation)
The claim follows from `FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full`.
-/
theorem FlagIntegralAntisymmetrize.full : FlagIntegralAntisymmetrize.Statement :=
  FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full

/- English proof (translation)
The claim follows from `FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full`.
-/
theorem FlagIntegralTopComponent.full : FlagIntegralTopComponent.Statement :=
  FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full

/- English proof (translation)
The claim follows from `FlagHomogeneousComponentMul.proof`.
-/
theorem FlagHomogeneousComponentMul.full : FlagHomogeneousComponentMul.Statement :=
  FlagHomogeneousComponentMul.proof

/- English proof (translation)
The claim follows from `FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full`.
-/
theorem FlagIntegralVandermondeMul.full : FlagIntegralVandermondeMul.Statement :=
  FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full

/- English proof (translation)
The claim follows from `FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full`.
-/
theorem FlagIntegralViaQuotient.full : FlagIntegralViaQuotient.Statement :=
  FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full

/- English proof (translation)
The claim follows from `FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full`.
-/
theorem FlagIntegralTopDegree.full : FlagIntegralTopDegree.Statement :=
  FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full

/- English proof (translation)
The claim follows from `FlagIntegralVandermondePos.proof`.
-/
theorem FlagIntegralVandermondePos.full : FlagIntegralVandermondePos.Statement :=
  FlagIntegralVandermondePos.proof

/- English proof (translation)
The claim follows from `IntegralIsDividedDifference.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full`.
-/
theorem IntegralIsDividedDifference.full : IntegralIsDividedDifference.Statement :=
  IntegralIsDividedDifference.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full

/- English proof (translation)
The claim follows from `FlagSwapDivisible.proof`.
-/
theorem FlagSwapDivisible.full : FlagSwapDivisible.Statement :=
  FlagSwapDivisible.proof

/- English proof (translation)
The claim follows from `FlagDiffPrime.proof`.
-/
theorem FlagDiffPrime.full : FlagDiffPrime.Statement :=
  FlagDiffPrime.proof

/- English proof (translation)
The claim follows from `FlagDiffNotDvd.proof`.
-/
theorem FlagDiffNotDvd.full : FlagDiffNotDvd.Statement :=
  FlagDiffNotDvd.proof

/- English proof (translation)
The claim follows from `FlagProdPrimesDvd.proof`.
-/
theorem FlagProdPrimesDvd.full : FlagProdPrimesDvd.Statement :=
  FlagProdPrimesDvd.proof

/- English proof (translation)
The claim follows from `FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full`.
-/
theorem FlagVandermondeDvd.full : FlagVandermondeDvd.Statement :=
  FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full

/- English proof (translation)
The claim follows from `FlagDividedDifferencePoly.proof FlagVandermondeDvd.full`.
-/
theorem FlagDividedDifferencePoly.full : FlagDividedDifferencePoly.Statement :=
  FlagDividedDifferencePoly.proof FlagVandermondeDvd.full

/- English proof (translation)
The claim follows from `FlagSymmetricMulAntisym.proof`.
-/
theorem FlagSymmetricMulAntisym.full : FlagSymmetricMulAntisym.Statement :=
  FlagSymmetricMulAntisym.proof

/- English proof (translation)
The claim follows from `FlagPowerSumSymmetric.proof`.
-/
theorem FlagPowerSumSymmetric.full : FlagPowerSumSymmetric.Statement :=
  FlagPowerSumSymmetric.proof

/- English proof (translation)
The claim follows from `FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full`.
-/
theorem FlagAntisymDecomposition.full : FlagAntisymDecomposition.Statement :=
  FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full

/- English proof (translation)
The claim follows from `FlagQuotientHomogeneous.proof`.
-/
theorem FlagQuotientHomogeneous.full : FlagQuotientHomogeneous.Statement :=
  FlagQuotientHomogeneous.proof

/- English proof (translation)
The claim follows from `FlagRestrictHomogeneous.proof`.
-/
theorem FlagRestrictHomogeneous.full : FlagRestrictHomogeneous.Statement :=
  FlagRestrictHomogeneous.proof

/- English proof (translation)
The claim follows from `FlagRestrictSymmetric.proof`.
-/
theorem FlagRestrictSymmetric.full : FlagRestrictSymmetric.Statement :=
  FlagRestrictSymmetric.proof

/- English proof (translation)
The claim follows from `FlagRestrictPowerSum.proof`.
-/
theorem FlagRestrictPowerSum.full : FlagRestrictPowerSum.Statement :=
  FlagRestrictPowerSum.proof

/- English proof (translation)
The claim follows from `FlagRestrictDecomposition.proof FlagRestrictPowerSum.full`.
-/
theorem FlagRestrictDecomposition.full : FlagRestrictDecomposition.Statement :=
  FlagRestrictDecomposition.proof FlagRestrictPowerSum.full

/- English proof (translation)
The claim follows from `FlagPowerSumPreimage.proof`.
-/
theorem FlagPowerSumPreimage.full : FlagPowerSumPreimage.Statement :=
  FlagPowerSumPreimage.proof

/- English proof (translation)
The claim follows from `FlagRestrictConstantCoeff.proof`.
-/
theorem FlagRestrictConstantCoeff.full : FlagRestrictConstantCoeff.Statement :=
  FlagRestrictConstantCoeff.proof

/- English proof (translation)
The claim follows from `LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full Fl …`.
-/
theorem LemmaA.full : LemmaA.Statement :=
  LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full FlagRestrictDecomposition.full FlagPowerSumPreimage.full FlagRestrictConstantCoeff.full FlagIntegralViaQuotient.full

/- English proof (translation)
The claim follows from `RestTermWellDefined.proof LemmaA.full`.
-/
theorem RestTermWellDefined.full : RestTermWellDefined.Statement :=
  RestTermWellDefined.proof LemmaA.full

/- English proof (translation)
The claim follows from `SchAevalSignedRename.proof`.
-/
theorem SchAevalSignedRename.full : SchAevalSignedRename.Statement :=
  SchAevalSignedRename.proof

/- English proof (translation)
The claim follows from `SchAntisymmetrizePlace.proof`.
-/
theorem SchAntisymmetrizePlace.full : SchAntisymmetrizePlace.Statement :=
  SchAntisymmetrizePlace.proof

/- English proof (translation)
The claim follows from `SchAlternantHomogeneous.proof`.
-/
theorem SchAlternantHomogeneous.full : SchAlternantHomogeneous.Statement :=
  SchAlternantHomogeneous.proof

/- English proof (translation)
The claim follows from `SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full`.
-/
theorem SchSmallBlockProduct.full : SchSmallBlockProduct.Statement :=
  SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full

/- English proof (translation)
The claim follows from `SchAlternantRenamePlace.proof`.
-/
theorem SchAlternantRenamePlace.full : SchAlternantRenamePlace.Statement :=
  SchAlternantRenamePlace.proof

/- English proof (translation)
The claim follows from `SchConcatExponent.proof`.
-/
theorem SchConcatExponent.full : SchConcatExponent.Statement :=
  SchConcatExponent.proof

/- English proof (translation)
The claim follows from `SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full`.
-/
theorem SchConcatAlternant.full : SchConcatAlternant.Statement :=
  SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full

/- English proof (translation)
The claim follows from `SchConcatAlternantZero.proof`.
-/
theorem SchConcatAlternantZero.full : SchConcatAlternantZero.Statement :=
  SchConcatAlternantZero.proof

/- English proof (translation)
The claim follows from `SchBlockVandermondeOne.proof`.
-/
theorem SchBlockVandermondeOne.full : SchBlockVandermondeOne.Statement :=
  SchBlockVandermondeOne.proof

/- English proof (translation)
The claim follows from `SchSchurHomogeneous.proof`.
-/
theorem SchSchurHomogeneous.full : SchSchurHomogeneous.Statement :=
  SchSchurHomogeneous.proof

/- English proof (translation)
The claim follows from `LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full`.
-/
theorem LemmaB.full : LemmaB.Statement :=
  LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full

/- English proof (translation)
The claim follows from `CombCardYoungCells.proof`.
-/
theorem CombCardYoungCells.full : CombCardYoungCells.Statement :=
  CombCardYoungCells.proof

/- English proof (translation)
The claim follows from `CombTableauRowCount.proof`.
-/
theorem CombTableauRowCount.full : CombTableauRowCount.Statement :=
  CombTableauRowCount.proof

/- English proof (translation)
The claim follows from `CombTableauRowPrefix.proof`.
-/
theorem CombTableauRowPrefix.full : CombTableauRowPrefix.Statement :=
  CombTableauRowPrefix.proof

/- English proof (translation)
The claim follows from `CombTableauRowLattice.proof`.
-/
theorem CombTableauRowLattice.full : CombTableauRowLattice.Statement :=
  CombTableauRowLattice.proof

/- English proof (translation)
The claim follows from `CombYoungRowCard.proof`.
-/
theorem CombYoungRowCard.full : CombYoungRowCard.Statement :=
  CombYoungRowCard.proof

/- English proof (translation)
The claim follows from `CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full`.
-/
theorem CombWordOfTableau.full : CombWordOfTableau.Statement :=
  CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full

/- English proof (translation)
The claim follows from `CombCellOfWordMem.proof`.
-/
theorem CombCellOfWordMem.full : CombCellOfWordMem.Statement :=
  CombCellOfWordMem.proof

/- English proof (translation)
The claim follows from `CombCellOfWordInj.proof`.
-/
theorem CombCellOfWordInj.full : CombCellOfWordInj.Statement :=
  CombCellOfWordInj.proof

/- English proof (translation)
The claim follows from `CombCellOfWordMono.proof`.
-/
theorem CombCellOfWordMono.full : CombCellOfWordMono.Statement :=
  CombCellOfWordMono.proof

/- English proof (translation)
The claim follows from `CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full`.
-/
theorem CombTableauOfWord.full : CombTableauOfWord.Statement :=
  CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full

/- English proof (translation)
The claim follows from `CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full`.
-/
theorem CombTableEqWords.full : CombTableEqWords.Statement :=
  CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full

/- English proof (translation)
The claim follows from `CombCfUpdateZero.proof`.
-/
theorem CombCfUpdateZero.full : CombCfUpdateZero.Statement :=
  CombCfUpdateZero.proof

/- English proof (translation)
The claim follows from `CombCfAtStair.proof CombCfUpdateZero.full`.
-/
theorem CombCfAtStair.full : CombCfAtStair.Statement :=
  CombCfAtStair.proof CombCfUpdateZero.full

/- English proof (translation)
The claim follows from `CombCfMonomialPsumOne.proof`.
-/
theorem CombCfMonomialPsumOne.full : CombCfMonomialPsumOne.Statement :=
  CombCfMonomialPsumOne.proof

/- English proof (translation)
The claim follows from `CombDetDescFactorial.proof`.
-/
theorem CombDetDescFactorial.full : CombDetDescFactorial.Statement :=
  CombDetDescFactorial.proof

/- English proof (translation)
The claim follows from `CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full`.
-/
theorem CombCfVandermondePsumOne.full : CombCfVandermondePsumOne.Statement :=
  CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full

/- English proof (translation)
The claim follows from `FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full`.
-/
theorem FrobeniusDimensionFormula.full : FrobeniusDimensionFormula.Statement :=
  FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full

/- English proof (translation)
The claim follows from `LemmaC.proof FrobeniusDimensionFormula.full`.
-/
theorem LemmaC.full : LemmaC.Statement :=
  LemmaC.proof FrobeniusDimensionFormula.full

/- English proof (translation)
The claim follows from `SchPowerSumHomWeighted.proof`.
-/
theorem SchPowerSumHomWeighted.full : SchPowerSumHomWeighted.Statement :=
  SchPowerSumHomWeighted.proof

/- English proof (translation)
The claim follows from `SchWeightedPreimage.proof SchPowerSumHomWeighted.full`.
-/
theorem SchWeightedPreimage.full : SchWeightedPreimage.Statement :=
  SchWeightedPreimage.proof SchPowerSumHomWeighted.full

/- English proof (translation)
The claim follows from `SchPowerSumAtRootsOfUnity.proof`.
-/
theorem SchPowerSumAtRootsOfUnity.full : SchPowerSumAtRootsOfUnity.Statement :=
  SchPowerSumAtRootsOfUnity.proof

/- English proof (translation)
The claim follows from `SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full`.
-/
theorem SchEvalPowerSumHom.full : SchEvalPowerSumHom.Statement :=
  SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full

/- English proof (translation)
The claim follows from `SchSchurRowsToK.proof`.
-/
theorem SchSchurRowsToK.full : SchSchurRowsToK.Statement :=
  SchSchurRowsToK.proof

/- English proof (translation)
The claim follows from `SchProdOneSubRootsOfUnity.proof`.
-/
theorem SchProdOneSubRootsOfUnity.full : SchProdOneSubRootsOfUnity.Statement :=
  SchProdOneSubRootsOfUnity.proof

/- English proof (translation)
The claim follows from `SchCompleteGenerating.proof`.
-/
theorem SchCompleteGenerating.full : SchCompleteGenerating.Statement :=
  SchCompleteGenerating.proof

/- English proof (translation)
The claim follows from `SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full`.
-/
theorem SchCompleteAtRootsOfUnity.full : SchCompleteAtRootsOfUnity.Statement :=
  SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full

/- English proof (translation)
The claim follows from `SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full`.
-/
theorem SchSchurEvalMatrix.full : SchSchurEvalMatrix.Statement :=
  SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full

/- English proof (translation)
The claim follows from `SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full`.
-/
theorem SchRootOfUnityBialternant.full : SchRootOfUnityBialternant.Statement :=
  SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full

/- English proof (translation)
The claim follows from `SchRootOfUnityRowsPerm.proof`.
-/
theorem SchRootOfUnityRowsPerm.full : SchRootOfUnityRowsPerm.Statement :=
  SchRootOfUnityRowsPerm.proof

/- English proof (translation)
The claim follows from `SchRootOfUnityRowsEq.proof`.
-/
theorem SchRootOfUnityRowsEq.full : SchRootOfUnityRowsEq.Statement :=
  SchRootOfUnityRowsEq.proof

/- English proof (translation)
The claim follows from `SchHookResidues.proof`.
-/
theorem SchHookResidues.full : SchHookResidues.Statement :=
  SchHookResidues.proof

/- English proof (translation)
The claim follows from `SchResidueCount.proof`.
-/
theorem SchResidueCount.full : SchResidueCount.Statement :=
  SchResidueCount.proof

/- English proof (translation)
The claim follows from `SchNonHookResidues.proof SchResidueCount.full`.
-/
theorem SchNonHookResidues.full : SchNonHookResidues.Statement :=
  SchNonHookResidues.proof SchResidueCount.full

/- English proof (translation)
The claim follows from `SchRootOfUnityVandermondeNe.proof`.
-/
theorem SchRootOfUnityVandermondeNe.full : SchRootOfUnityVandermondeNe.Statement :=
  SchRootOfUnityVandermondeNe.proof

/- English proof (translation)
The claim follows from `SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full`.
-/
theorem SchJTMatrixDetAtRoots.full : SchJTMatrixDetAtRoots.Statement :=
  SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full

/- English proof (translation)
The claim follows from `SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full`.
-/
theorem SchSchurAtRootsOfUnity.full : SchSchurAtRootsOfUnity.Statement :=
  SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full

/- English proof (translation)
The claim follows from `SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full`.
-/
theorem SchurPowerSumCoefficient.full : SchurPowerSumCoefficient.Statement :=
  SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full

/- English proof (translation)
The claim follows from `CombHookShapeFacts.proof`.
-/
theorem CombHookShapeFacts.full : CombHookShapeFacts.Statement :=
  CombHookShapeFacts.proof

/- English proof (translation)
The claim follows from `CombHookBranch.proof CombHookShapeFacts.full`.
-/
theorem CombHookBranch.full : CombHookBranch.Statement :=
  CombHookBranch.proof CombHookShapeFacts.full

/- English proof (translation)
The claim follows from `CombHookCount.proof CombHookShapeFacts.full CombHookBranch.full`.
-/
theorem CombHookCount.full : CombHookCount.Statement :=
  CombHookCount.proof CombHookShapeFacts.full CombHookBranch.full

/- English proof (translation)
The claim follows from `HookDimensionSum.proof CombTableEqWords.full CombHookShapeFacts.full CombHookCount.full`.
-/
theorem HookDimensionSum.full : HookDimensionSum.Statement :=
  HookDimensionSum.proof CombTableEqWords.full CombHookShapeFacts.full CombHookCount.full

/- English proof (translation)
The claim follows from `SchStrictAntiSplit.proof`.
-/
theorem SchStrictAntiSplit.full : SchStrictAntiSplit.Statement :=
  SchStrictAntiSplit.proof

/- English proof (translation)
The claim follows from `SchAltPartitionExpansion.proof SchStrictAntiSplit.full`.
-/
theorem SchAltPartitionExpansion.full : SchAltPartitionExpansion.Statement :=
  SchAltPartitionExpansion.proof SchStrictAntiSplit.full

/- English proof (translation)
The claim follows from `FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full`.
-/
theorem FrobeniusCharacterFormula.full : FrobeniusCharacterFormula.Statement :=
  FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full

/- English proof (translation)
The claim follows from `CombSortLe.proof`.
-/
theorem CombSortLe.full : CombSortLe.Statement :=
  CombSortLe.proof

/- English proof (translation)
The claim follows from `Comb.CombSortShift.proof CombSortLe.full`.
-/
theorem CombSortShift.full : CombSortShift.Statement :=
  Comb.CombSortShift.proof CombSortLe.full

/- English proof (translation)
The claim follows from `CombSortShiftDistinct.proof`.
-/
theorem CombSortShiftDistinct.full : CombSortShiftDistinct.Statement :=
  CombSortShiftDistinct.proof

/- English proof (translation)
The claim follows from `CombPcntAppend.proof`.
-/
theorem CombPcntAppend.full : CombPcntAppend.Statement :=
  CombPcntAppend.proof

/- English proof (translation)
The claim follows from `CombExtendWord.proof CombPcntAppend.full`.
-/
theorem CombExtendWord.full : CombExtendWord.Statement :=
  CombExtendWord.proof CombPcntAppend.full

/- English proof (translation)
The claim follows from `CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full`.
-/
theorem CombStripSum.full : CombStripSum.Statement :=
  CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full

/- English proof (translation)
The claim follows from `CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full`.
-/
theorem CombCfBound.full : CombCfBound.Statement :=
  CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full

/- English proof (translation)
The claim follows from `CharacterBound.proof CombTableEqWords.full CombCfBound.full`.
-/
theorem CharacterBound.full : CharacterBound.Statement :=
  CharacterBound.proof CombTableEqWords.full CombCfBound.full

/- English proof (translation)
The claim follows from `CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full`.
-/
theorem CharacterAtIdentity.full : CharacterAtIdentity.Statement :=
  CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full

/- English proof (translation)
The claim follows from `CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full`.
-/
theorem CoinvAboveTop.full : CoinvAboveTop.Statement :=
  CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

/- English proof (translation)
The claim follows from `VandermondeOfHomogeneous.proof`.
-/
theorem VandermondeOfHomogeneous.full : VandermondeOfHomogeneous.Statement :=
  VandermondeOfHomogeneous.proof

/- English proof (translation)
The claim follows from `RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full`.
-/
theorem RestPolynomialHomogeneous.full : RestPolynomialHomogeneous.Statement :=
  RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full

/- English proof (translation)
The claim follows from `RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full`.
-/
theorem RestPolynomialHomogeneousDecomposition.full : RestPolynomialHomogeneousDecomposition.Statement :=
  RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full

/- English proof (translation)
The claim follows from `RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full`.
-/
theorem RestPolynomialDecomposes.full : RestPolynomialDecomposes.Statement :=
  RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full

/- English proof (translation)
The claim follows from `SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange`.
-/
theorem SameFactorFormula.full : SameFactorFormula.Statement :=
  SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `SchurSignCoefficient.proof SchurPowerSumCoefficient.full`.
-/
theorem SchurSignCoefficient.full : SchurSignCoefficient.Statement :=
  SchurSignCoefficient.proof SchurPowerSumCoefficient.full

/- English proof (translation)
The claim follows from `HookTableauCount.proof FrobeniusDimensionFormula.full`.
-/
theorem HookTableauCount.full : HookTableauCount.Statement :=
  HookTableauCount.proof FrobeniusDimensionFormula.full

/- English proof (translation)
The claim follows from `HookSumBound.proof LemmaC.full HookTableauCount.full`.
-/
theorem HookSumBound.full : HookSumBound.Statement :=
  HookSumBound.proof LemmaC.full HookTableauCount.full

/- English proof (translation)
The claim follows from `SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full`.
-/
theorem SameFactorBound.full : SameFactorBound.Statement :=
  SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
The claim follows from `OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange`.
-/
theorem OtherFactorFormula.full : OtherFactorFormula.Statement :=
  OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full`.
-/
theorem OtherFactorBound.full : OtherFactorBound.Statement :=
  OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
The claim follows from `ShiftSumRule.proof ShiftTotalValues.intersectionNumber_baseChange FlagIntegralKillsPowerSums.intersectionNumber_baseChange`.
-/
theorem ShiftSumRule.full : ShiftSumRule.Statement :=
  ShiftSumRule.proof ShiftTotalValues.intersectionNumber_baseChange FlagIntegralKillsPowerSums.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `LinearTermValue.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full`.
-/
theorem LinearTermValue.full : LinearTermValue.Statement :=
  LinearTermValue.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full

/- English proof (translation)
The claim follows from `HookCharacterSumIdentity.proof ShiftSumRule.full LinearTermValue.full SameFactorFormula.full SchurSignCoefficient.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full`.
-/
theorem HookCharacterSumIdentity.full : HookCharacterSumIdentity.Statement :=
  HookCharacterSumIdentity.proof ShiftSumRule.full LinearTermValue.full SameFactorFormula.full SchurSignCoefficient.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
The claim follows from `CombVandermondeSucc.proof`.
-/
theorem CombVandermondeSucc.full : CombVandermondeSucc.Statement :=
  CombVandermondeSucc.proof

/- English proof (translation)
The claim follows from `TotalIdentity.proof FrobeniusDimensionFormula.full CombVandermondeSucc.full`.
-/
theorem TotalIdentity.full : TotalIdentity.Statement :=
  TotalIdentity.proof FrobeniusDimensionFormula.full CombVandermondeSucc.full

/- English proof (translation)
The claim follows from `RestInnerTsumBound.proof`.
-/
theorem RestInnerTsumBound.full : RestInnerTsumBound.Statement :=
  RestInnerTsumBound.proof

/- English proof (translation)
The claim follows from `RestKSumBound.proof`.
-/
theorem RestKSumBound.full : RestKSumBound.Statement :=
  RestKSumBound.proof

/- English proof (translation)
The claim follows from `RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full`.
-/
theorem RestPrimeBoundOfFactor.full : RestPrimeBoundOfFactor.Statement :=
  RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full

/- English proof (translation)
The claim follows from `RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full`.
-/
theorem RestPrimeBound.full : RestPrimeBound.Statement :=
  RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full

/- English proof (translation)
The claim follows from `RestBoundOfPrimeBound.proof`.
-/
theorem RestBoundOfPrimeBound.full : RestBoundOfPrimeBound.Statement :=
  RestBoundOfPrimeBound.proof

/- English proof (translation)
The claim follows from `RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full`.
-/
theorem RestBound.full : RestBound.Statement :=
  RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full

/- English proof (translation)
The claim follows from `FlagIntegralKillsPowerSums.intersectionNumber_baseChange`.
-/
theorem FlagIntegralKillsPowerSums.full : FlagIntegralKillsPowerSums.Statement :=
  FlagIntegralKillsPowerSums.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `DividedDifferenceOfVandermonde.intersectionNumber_baseChange`.
-/
theorem DividedDifferenceOfVandermonde.full : DividedDifferenceOfVandermonde.Statement :=
  DividedDifferenceOfVandermonde.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `XBound.intersectionNumber_baseChange`.
-/
theorem XBound.full : XBound.Statement :=
  XBound.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `XOverPrime.intersectionNumber_baseChange`.
-/
theorem XOverPrime.full : XOverPrime.Statement :=
  XOverPrime.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `GeometricTail.intersectionNumber_baseChange`.
-/
theorem GeometricTail.full : GeometricTail.Statement :=
  GeometricTail.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `ExponentialTail.intersectionNumber_baseChange`.
-/
theorem ExponentialTail.full : ExponentialTail.Statement :=
  ExponentialTail.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `ChebyshevThetaBound.intersectionNumber_baseChange`.
-/
theorem ChebyshevThetaBound.full : ChebyshevThetaBound.Statement :=
  ChebyshevThetaBound.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `PrimeLogSquareTail.intersectionNumber_baseChange`.
-/
theorem PrimeLogSquareTail.full : PrimeLogSquareTail.Statement :=
  PrimeLogSquareTail.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `RestConstants.intersectionNumber_baseChange`.
-/
theorem RestConstants.full : RestConstants.Statement :=
  RestConstants.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `IntegerLogSquareTail.intersectionNumber_baseChange`.
-/
theorem IntegerLogSquareTail.full : IntegerLogSquareTail.Statement :=
  IntegerLogSquareTail.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `ShiftTotalValues.intersectionNumber_baseChange`.
-/
theorem ShiftTotalValues.full : ShiftTotalValues.Statement :=
  ShiftTotalValues.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `FibreTranslationInvariance.intersectionNumber_baseChange`.
-/
theorem FibreTranslationInvariance.full : FibreTranslationInvariance.Statement :=
  FibreTranslationInvariance.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `PlueckerCauchyBinet.intersectionNumber_baseChange`.
-/
theorem PlueckerCauchyBinet.full : PlueckerCauchyBinet.Statement :=
  PlueckerCauchyBinet.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `PlueckerHadamard.intersectionNumber_baseChange`.
-/
theorem PlueckerHadamard.full : PlueckerHadamard.Statement :=
  PlueckerHadamard.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `SmallRankBound.intersectionNumber_baseChange`.
-/
theorem SmallRankBound.full : SmallRankBound.Statement :=
  SmallRankBound.intersectionNumber_baseChange

/- English proof (translation)
The claim follows from `SmallRankWeakHypothesis.intersectionNumber_baseChange`.
-/
theorem SmallRankWeakHypothesis.full : SmallRankWeakHypothesis.Statement :=
  SmallRankWeakHypothesis.intersectionNumber_baseChange

end RestTerms

end GroundTheory.Heights₂.Heights
