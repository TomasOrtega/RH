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
A detailed English derivation is pending.
-/
theorem CoinvStepReduction.full : CoinvStepReduction.Statement :=
  CoinvStepReduction.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvMonomialReduction.full : CoinvMonomialReduction.Statement :=
  CoinvMonomialReduction.proof CoinvStepReduction.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvPolynomialReduction.full : CoinvPolynomialReduction.Statement :=
  CoinvPolynomialReduction.proof CoinvMonomialReduction.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvIdealRepresentation.full : CoinvIdealRepresentation.Statement :=
  CoinvIdealRepresentation.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HomogeneousComponentMul.full : HomogeneousComponentMul.Statement :=
  HomogeneousComponentMul.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvIdealComponent.full : CoinvIdealComponent.Statement :=
  CoinvIdealComponent.proof CoinvIdealRepresentation.full HomogeneousComponentMul.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvStaircaseDegree.full : CoinvStaircaseDegree.Statement :=
  CoinvStaircaseDegree.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvStaircaseComponent.full : CoinvStaircaseComponent.Statement :=
  CoinvStaircaseComponent.proof CoinvStaircaseDegree.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvAtTop.full : CoinvAtTop.Statement :=
  CoinvAtTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvariantTopDegree.full : CoinvariantTopDegree.Statement :=
  CoinvariantTopDegree.proof CoinvAtTop.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagCoeffBlockPermute.full : FlagCoeffBlockPermute.Statement :=
  FlagCoeffBlockPermute.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagAltCoeffInjective.full : FlagAltCoeffInjective.Statement :=
  FlagAltCoeffInjective.proof FlagCoeffBlockPermute.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagInjSumBound.full : FlagInjSumBound.Statement :=
  FlagInjSumBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagStaircaseOrbit.full : FlagStaircaseOrbit.Statement :=
  FlagStaircaseOrbit.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagVandermondeHomogeneous.full : FlagVandermondeHomogeneous.Statement :=
  FlagVandermondeHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagAltTopDegree.full : FlagAltTopDegree.Statement :=
  FlagAltTopDegree.proof FlagCoeffBlockPermute.full FlagAltCoeffInjective.full FlagInjSumBound.full FlagStaircaseOrbit.full FlagVandermondeHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagAntisymHomogeneous.full : FlagAntisymHomogeneous.Statement :=
  FlagAntisymHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralPermute.full : FlagIntegralPermute.Statement :=
  FlagIntegralPermute.proof FlagCoeffBlockPermute.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralAntisymmetrize.full : FlagIntegralAntisymmetrize.Statement :=
  FlagIntegralAntisymmetrize.proof FlagIntegralPermute.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralTopComponent.full : FlagIntegralTopComponent.Statement :=
  FlagIntegralTopComponent.proof FlagVandermondeHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagHomogeneousComponentMul.full : FlagHomogeneousComponentMul.Statement :=
  FlagHomogeneousComponentMul.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralVandermondeMul.full : FlagIntegralVandermondeMul.Statement :=
  FlagIntegralVandermondeMul.proof FlagIntegralTopComponent.full FlagHomogeneousComponentMul.full FlagVandermondeHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralViaQuotient.full : FlagIntegralViaQuotient.Statement :=
  FlagIntegralViaQuotient.proof FlagIntegralAntisymmetrize.full FlagIntegralVandermondeMul.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralTopDegree.full : FlagIntegralTopDegree.Statement :=
  FlagIntegralTopDegree.proof FlagAltTopDegree.full FlagAntisymHomogeneous.full FlagIntegralViaQuotient.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralVandermondePos.full : FlagIntegralVandermondePos.Statement :=
  FlagIntegralVandermondePos.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntegralIsDividedDifference.full : IntegralIsDividedDifference.Statement :=
  IntegralIsDividedDifference.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagSwapDivisible.full : FlagSwapDivisible.Statement :=
  FlagSwapDivisible.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagDiffPrime.full : FlagDiffPrime.Statement :=
  FlagDiffPrime.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagDiffNotDvd.full : FlagDiffNotDvd.Statement :=
  FlagDiffNotDvd.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagProdPrimesDvd.full : FlagProdPrimesDvd.Statement :=
  FlagProdPrimesDvd.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagVandermondeDvd.full : FlagVandermondeDvd.Statement :=
  FlagVandermondeDvd.proof FlagSwapDivisible.full FlagDiffPrime.full FlagDiffNotDvd.full FlagProdPrimesDvd.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagDividedDifferencePoly.full : FlagDividedDifferencePoly.Statement :=
  FlagDividedDifferencePoly.proof FlagVandermondeDvd.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagSymmetricMulAntisym.full : FlagSymmetricMulAntisym.Statement :=
  FlagSymmetricMulAntisym.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagPowerSumSymmetric.full : FlagPowerSumSymmetric.Statement :=
  FlagPowerSumSymmetric.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagAntisymDecomposition.full : FlagAntisymDecomposition.Statement :=
  FlagAntisymDecomposition.proof FlagSymmetricMulAntisym.full FlagPowerSumSymmetric.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagQuotientHomogeneous.full : FlagQuotientHomogeneous.Statement :=
  FlagQuotientHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagRestrictHomogeneous.full : FlagRestrictHomogeneous.Statement :=
  FlagRestrictHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagRestrictSymmetric.full : FlagRestrictSymmetric.Statement :=
  FlagRestrictSymmetric.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagRestrictPowerSum.full : FlagRestrictPowerSum.Statement :=
  FlagRestrictPowerSum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagRestrictDecomposition.full : FlagRestrictDecomposition.Statement :=
  FlagRestrictDecomposition.proof FlagRestrictPowerSum.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagPowerSumPreimage.full : FlagPowerSumPreimage.Statement :=
  FlagPowerSumPreimage.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagRestrictConstantCoeff.full : FlagRestrictConstantCoeff.Statement :=
  FlagRestrictConstantCoeff.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaA.full : LemmaA.Statement :=
  LemmaA.proof FlagIntegralTopDegree.full FlagIntegralVandermondePos.full FlagDividedDifferencePoly.full FlagAntisymDecomposition.full FlagVandermondeHomogeneous.full FlagAntisymHomogeneous.full FlagQuotientHomogeneous.full FlagRestrictHomogeneous.full FlagRestrictSymmetric.full FlagRestrictDecomposition.full FlagPowerSumPreimage.full FlagRestrictConstantCoeff.full FlagIntegralViaQuotient.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestTermWellDefined.full : RestTermWellDefined.Statement :=
  RestTermWellDefined.proof LemmaA.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchAevalSignedRename.full : SchAevalSignedRename.Statement :=
  SchAevalSignedRename.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchAntisymmetrizePlace.full : SchAntisymmetrizePlace.Statement :=
  SchAntisymmetrizePlace.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchAlternantHomogeneous.full : SchAlternantHomogeneous.Statement :=
  SchAlternantHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchSmallBlockProduct.full : SchSmallBlockProduct.Statement :=
  SchSmallBlockProduct.proof SchAevalSignedRename.full SchAlternantHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchAlternantRenamePlace.full : SchAlternantRenamePlace.Statement :=
  SchAlternantRenamePlace.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchConcatExponent.full : SchConcatExponent.Statement :=
  SchConcatExponent.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchConcatAlternant.full : SchConcatAlternant.Statement :=
  SchConcatAlternant.proof SchAlternantRenamePlace.full SchConcatExponent.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchConcatAlternantZero.full : SchConcatAlternantZero.Statement :=
  SchConcatAlternantZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchBlockVandermondeOne.full : SchBlockVandermondeOne.Statement :=
  SchBlockVandermondeOne.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchSchurHomogeneous.full : SchSchurHomogeneous.Statement :=
  SchSchurHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaB.full : LemmaB.Statement :=
  LemmaB.proof SchAevalSignedRename.full SchAntisymmetrizePlace.full SchSmallBlockProduct.full SchConcatAlternant.full SchConcatAlternantZero.full SchBlockVandermondeOne.full SchSchurHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCardYoungCells.full : CombCardYoungCells.Statement :=
  CombCardYoungCells.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombTableauRowCount.full : CombTableauRowCount.Statement :=
  CombTableauRowCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombTableauRowPrefix.full : CombTableauRowPrefix.Statement :=
  CombTableauRowPrefix.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombTableauRowLattice.full : CombTableauRowLattice.Statement :=
  CombTableauRowLattice.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombYoungRowCard.full : CombYoungRowCard.Statement :=
  CombYoungRowCard.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombWordOfTableau.full : CombWordOfTableau.Statement :=
  CombWordOfTableau.proof CombTableauRowCount.full CombTableauRowPrefix.full CombTableauRowLattice.full CombYoungRowCard.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCellOfWordMem.full : CombCellOfWordMem.Statement :=
  CombCellOfWordMem.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCellOfWordInj.full : CombCellOfWordInj.Statement :=
  CombCellOfWordInj.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCellOfWordMono.full : CombCellOfWordMono.Statement :=
  CombCellOfWordMono.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombTableauOfWord.full : CombTableauOfWord.Statement :=
  CombTableauOfWord.proof CombCellOfWordMem.full CombCellOfWordInj.full CombCellOfWordMono.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombTableEqWords.full : CombTableEqWords.Statement :=
  CombTableEqWords.proof CombCardYoungCells.full CombWordOfTableau.full CombTableauOfWord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCfUpdateZero.full : CombCfUpdateZero.Statement :=
  CombCfUpdateZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCfAtStair.full : CombCfAtStair.Statement :=
  CombCfAtStair.proof CombCfUpdateZero.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCfMonomialPsumOne.full : CombCfMonomialPsumOne.Statement :=
  CombCfMonomialPsumOne.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombDetDescFactorial.full : CombDetDescFactorial.Statement :=
  CombDetDescFactorial.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCfVandermondePsumOne.full : CombCfVandermondePsumOne.Statement :=
  CombCfVandermondePsumOne.proof CombCfMonomialPsumOne.full CombDetDescFactorial.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FrobeniusDimensionFormula.full : FrobeniusDimensionFormula.Statement :=
  FrobeniusDimensionFormula.proof CombTableEqWords.full CombCfAtStair.full CombCfVandermondePsumOne.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaC.full : LemmaC.Statement :=
  LemmaC.proof FrobeniusDimensionFormula.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchPowerSumHomWeighted.full : SchPowerSumHomWeighted.Statement :=
  SchPowerSumHomWeighted.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchWeightedPreimage.full : SchWeightedPreimage.Statement :=
  SchWeightedPreimage.proof SchPowerSumHomWeighted.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchPowerSumAtRootsOfUnity.full : SchPowerSumAtRootsOfUnity.Statement :=
  SchPowerSumAtRootsOfUnity.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchEvalPowerSumHom.full : SchEvalPowerSumHom.Statement :=
  SchEvalPowerSumHom.proof SchPowerSumAtRootsOfUnity.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchSchurRowsToK.full : SchSchurRowsToK.Statement :=
  SchSchurRowsToK.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchProdOneSubRootsOfUnity.full : SchProdOneSubRootsOfUnity.Statement :=
  SchProdOneSubRootsOfUnity.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchCompleteGenerating.full : SchCompleteGenerating.Statement :=
  SchCompleteGenerating.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchCompleteAtRootsOfUnity.full : SchCompleteAtRootsOfUnity.Statement :=
  SchCompleteAtRootsOfUnity.proof SchProdOneSubRootsOfUnity.full SchCompleteGenerating.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchSchurEvalMatrix.full : SchSchurEvalMatrix.Statement :=
  SchSchurEvalMatrix.proof SchCompleteAtRootsOfUnity.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchRootOfUnityBialternant.full : SchRootOfUnityBialternant.Statement :=
  SchRootOfUnityBialternant.proof SchSchurEvalMatrix.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchRootOfUnityRowsPerm.full : SchRootOfUnityRowsPerm.Statement :=
  SchRootOfUnityRowsPerm.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchRootOfUnityRowsEq.full : SchRootOfUnityRowsEq.Statement :=
  SchRootOfUnityRowsEq.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchHookResidues.full : SchHookResidues.Statement :=
  SchHookResidues.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchResidueCount.full : SchResidueCount.Statement :=
  SchResidueCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchNonHookResidues.full : SchNonHookResidues.Statement :=
  SchNonHookResidues.proof SchResidueCount.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchRootOfUnityVandermondeNe.full : SchRootOfUnityVandermondeNe.Statement :=
  SchRootOfUnityVandermondeNe.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchJTMatrixDetAtRoots.full : SchJTMatrixDetAtRoots.Statement :=
  SchJTMatrixDetAtRoots.proof SchRootOfUnityBialternant.full SchRootOfUnityRowsPerm.full SchRootOfUnityRowsEq.full SchHookResidues.full SchNonHookResidues.full SchRootOfUnityVandermondeNe.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchSchurAtRootsOfUnity.full : SchSchurAtRootsOfUnity.Statement :=
  SchSchurAtRootsOfUnity.proof SchSchurRowsToK.full SchSchurEvalMatrix.full SchJTMatrixDetAtRoots.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchurPowerSumCoefficient.full : SchurPowerSumCoefficient.Statement :=
  SchurPowerSumCoefficient.proof SchWeightedPreimage.full SchEvalPowerSumHom.full SchSchurHomogeneous.full SchSchurAtRootsOfUnity.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombHookShapeFacts.full : CombHookShapeFacts.Statement :=
  CombHookShapeFacts.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombHookBranch.full : CombHookBranch.Statement :=
  CombHookBranch.proof CombHookShapeFacts.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombHookCount.full : CombHookCount.Statement :=
  CombHookCount.proof CombHookShapeFacts.full CombHookBranch.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HookDimensionSum.full : HookDimensionSum.Statement :=
  HookDimensionSum.proof CombTableEqWords.full CombHookShapeFacts.full CombHookCount.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchStrictAntiSplit.full : SchStrictAntiSplit.Statement :=
  SchStrictAntiSplit.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchAltPartitionExpansion.full : SchAltPartitionExpansion.Statement :=
  SchAltPartitionExpansion.proof SchStrictAntiSplit.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FrobeniusCharacterFormula.full : FrobeniusCharacterFormula.Statement :=
  FrobeniusCharacterFormula.proof SchAltPartitionExpansion.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombSortLe.full : CombSortLe.Statement :=
  CombSortLe.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombSortShift.full : CombSortShift.Statement :=
  Comb.CombSortShift.proof CombSortLe.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombSortShiftDistinct.full : CombSortShiftDistinct.Statement :=
  CombSortShiftDistinct.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombPcntAppend.full : CombPcntAppend.Statement :=
  CombPcntAppend.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombExtendWord.full : CombExtendWord.Statement :=
  CombExtendWord.proof CombPcntAppend.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombStripSum.full : CombStripSum.Statement :=
  CombStripSum.proof CombCfAtStair.full CombSortShift.full CombSortShiftDistinct.full CombExtendWord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombCfBound.full : CombCfBound.Statement :=
  CombCfBound.proof CombCfAtStair.full CombSortShift.full CombStripSum.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CharacterBound.full : CharacterBound.Statement :=
  CharacterBound.proof CombTableEqWords.full CombCfBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CharacterAtIdentity.full : CharacterAtIdentity.Statement :=
  CharacterAtIdentity.proof CombTableEqWords.full CombCfAtStair.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoinvAboveTop.full : CoinvAboveTop.Statement :=
  CoinvAboveTop.proof CoinvPolynomialReduction.full CoinvIdealComponent.full CoinvStaircaseComponent.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VandermondeOfHomogeneous.full : VandermondeOfHomogeneous.Statement :=
  VandermondeOfHomogeneous.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPolynomialHomogeneous.full : RestPolynomialHomogeneous.Statement :=
  RestPolynomialHomogeneous.proof VandermondeOfHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPolynomialHomogeneousDecomposition.full : RestPolynomialHomogeneousDecomposition.Statement :=
  RestPolynomialHomogeneousDecomposition.proof CoinvAboveTop.full RestPolynomialHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPolynomialDecomposes.full : RestPolynomialDecomposes.Statement :=
  RestPolynomialDecomposes.proof RestPolynomialHomogeneousDecomposition.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SameFactorFormula.full : SameFactorFormula.Statement :=
  SameFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SchurSignCoefficient.full : SchurSignCoefficient.Statement :=
  SchurSignCoefficient.proof SchurPowerSumCoefficient.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HookTableauCount.full : HookTableauCount.Statement :=
  HookTableauCount.proof FrobeniusDimensionFormula.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HookSumBound.full : HookSumBound.Statement :=
  HookSumBound.proof LemmaC.full HookTableauCount.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SameFactorBound.full : SameFactorBound.Statement :=
  SameFactorBound.proof SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OtherFactorFormula.full : OtherFactorFormula.Statement :=
  OtherFactorFormula.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full RectangleTablePos.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OtherFactorBound.full : OtherFactorBound.Statement :=
  OtherFactorBound.proof OtherFactorFormula.full SameFactorFormula.full SchurSignCoefficient.full CharacterBound.full HookSumBound.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ShiftSumRule.full : ShiftSumRule.Statement :=
  ShiftSumRule.proof ShiftTotalValues.intersectionNumber_baseChange FlagIntegralKillsPowerSums.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LinearTermValue.full : LinearTermValue.Statement :=
  LinearTermValue.proof LemmaA.full LemmaB.full FrobeniusCharacterFormula.full CharacterAtIdentity.full VandermondeOfHomogeneous.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HookCharacterSumIdentity.full : HookCharacterSumIdentity.Statement :=
  HookCharacterSumIdentity.proof ShiftSumRule.full LinearTermValue.full SameFactorFormula.full SchurSignCoefficient.full RectangleTablePos.intersectionNumber_baseChange RestPolynomialDecomposes.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CombVandermondeSucc.full : CombVandermondeSucc.Statement :=
  CombVandermondeSucc.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TotalIdentity.full : TotalIdentity.Statement :=
  TotalIdentity.proof FrobeniusDimensionFormula.full CombVandermondeSucc.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestInnerTsumBound.full : RestInnerTsumBound.Statement :=
  RestInnerTsumBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestKSumBound.full : RestKSumBound.Statement :=
  RestKSumBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPrimeBoundOfFactor.full : RestPrimeBoundOfFactor.Statement :=
  RestPrimeBoundOfFactor.proof RestInnerTsumBound.full RestKSumBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestPrimeBound.full : RestPrimeBound.Statement :=
  RestPrimeBound.proof RestPrimeBoundOfFactor.full SameFactorBound.full OtherFactorBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestBoundOfPrimeBound.full : RestBoundOfPrimeBound.Statement :=
  RestBoundOfPrimeBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestBound.full : RestBound.Statement :=
  RestBound.proof RestPrimeBound.full RestBoundOfPrimeBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FlagIntegralKillsPowerSums.full : FlagIntegralKillsPowerSums.Statement :=
  FlagIntegralKillsPowerSums.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DividedDifferenceOfVandermonde.full : DividedDifferenceOfVandermonde.Statement :=
  DividedDifferenceOfVandermonde.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem XBound.full : XBound.Statement :=
  XBound.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem XOverPrime.full : XOverPrime.Statement :=
  XOverPrime.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeometricTail.full : GeometricTail.Statement :=
  GeometricTail.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ExponentialTail.full : ExponentialTail.Statement :=
  ExponentialTail.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChebyshevThetaBound.full : ChebyshevThetaBound.Statement :=
  ChebyshevThetaBound.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PrimeLogSquareTail.full : PrimeLogSquareTail.Statement :=
  PrimeLogSquareTail.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RestConstants.full : RestConstants.Statement :=
  RestConstants.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntegerLogSquareTail.full : IntegerLogSquareTail.Statement :=
  IntegerLogSquareTail.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ShiftTotalValues.full : ShiftTotalValues.Statement :=
  ShiftTotalValues.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FibreTranslationInvariance.full : FibreTranslationInvariance.Statement :=
  FibreTranslationInvariance.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PlueckerCauchyBinet.full : PlueckerCauchyBinet.Statement :=
  PlueckerCauchyBinet.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PlueckerHadamard.full : PlueckerHadamard.Statement :=
  PlueckerHadamard.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SmallRankBound.full : SmallRankBound.Statement :=
  SmallRankBound.intersectionNumber_baseChange

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SmallRankWeakHypothesis.full : SmallRankWeakHypothesis.Statement :=
  SmallRankWeakHypothesis.intersectionNumber_baseChange

end RestTerms

end GroundTheory.Heights₂.Heights
