import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PAddHeightsridge
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatNmSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PChartLatSection
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PDualBasisExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightedHomogeneousComponentMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Imports
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsArithVarOfRingKrullDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PFibreCompDimZ
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.DetGramLeProdNormSq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VolumeFundamentalDomainEq
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroAlt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroBis
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PHomogGeneratorsExist
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLatticeLineExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineDegreeBundle
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineIdealDual
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockModel
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockStandard
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PPointHeightDegree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PReadsMul
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PSectionSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartPowNeZero
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartMonomialMemOfNotIsLive
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemPointsOfGeneratorsVanish
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicNew
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsFormOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.NormSqEvalConeScale
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtMapLiftOldOfIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExtVal
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.WeightEqMapDomain
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AnalyticAtEvalConeComp
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LiftOldChartMonomialMemPrimeCompl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousAeval
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroTer
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.BirationalOfBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousSepBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.VarsSubsetRangeBlockIncl
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeChartMonomialNeZeroMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.CardLeOfSeparated
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MonomialValuesOneBlock
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusMetric
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSec
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSmall
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PYPlusSupSmall
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartFormEvalAgree
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LinearIndependentOfMemSpan
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.HilbDegreeBoundAltOfStatement
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsWeightedHomogeneousMonomialOf
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsOneBlockLinMonomial
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsNatMulIsIntegralFin
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LatticePointPairForms
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ChartRingDescriptionAltHolds
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MapCompExtMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.EvalConeConj
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsFurther
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsExtra
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsRest
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.FiniteTwistsDegreeFormOfFirst
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemChartRingZOfMemChartRing
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.MemConePointsProjIdealIff
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.RenameBlockIsWeightedHomogeneous
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.LocalChangeOfVectorSpace
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ImportsLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `IntDomainDim.proof`.
-/
theorem IntDomainDim.full : IntDomainDim.Statement :=
  IntDomainDim.proof

/- English proof (translation)
The claim follows from `ConeTrdeg.proof`.
-/
theorem ConeTrdeg.full : ConeTrdeg.Statement :=
  ConeTrdeg.proof

/- English proof (translation)
The claim follows from `FibreCompDimZ.proof`.
-/
theorem FibreCompDimZ.full : FibreCompDimZ.Statement :=
  FibreCompDimZ.proof

/- English proof (translation)
The claim follows from `WeightedDegree.proof`.
-/
theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.proof

/- English proof (translation)
The claim follows from `ChartFormsAlt.proof`.
-/
theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.proof

/- English proof (translation)
The claim follows from `ChartCrossRatio.proof`.
-/
theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.proof

/- English proof (translation)
The claim follows from `ChartVanishing.proof`.
-/
theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.proof

/- English proof (translation)
The claim follows from `ChartPrimality.proof`.
-/
theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.proof

/- English proof (translation)
The claim follows from `ExtensionDimension.proof`.
-/
theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.proof

/- English proof (translation)
The claim follows from `ChartRingDescription.proof`.
-/
theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.proof

/- English proof (translation)
The claim follows from `HomogGeneratorsExist.proof`.
-/
theorem HomogGeneratorsExist.full : HomogGeneratorsExist.Statement :=
  HomogGeneratorsExist.proof

/- English proof (translation)
The claim follows from `SectionCycle.proof`.
-/
theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.proof

/- English proof (translation)
The claim follows from `BlockSurjectivity.proof`.
-/
theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.proof

/- English proof (translation)
The claim follows from `SectionInjectivity.proof`.
-/
theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.proof

/- English proof (translation)
The claim follows from `LatticePacking.proof`.
-/
theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.proof

/- English proof (translation)
The claim follows from `HadamardGramBound.proof`.
-/
theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.proof

/- English proof (translation)
The claim follows from `MonomialMap.proof`.
-/
theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.proof

/- English proof (translation)
The claim follows from `MonomialMapNorm.proof`.
-/
theorem MonomialMapNorm.full : MonomialMapNorm.Statement :=
  MonomialMapNorm.proof

/- English proof (translation)
The claim follows from `SpanningAtDominantWeight.proof`.
-/
theorem SpanningAtDominantWeight.full : SpanningAtDominantWeight.Statement :=
  SpanningAtDominantWeight.proof

/- English proof (translation)
The claim follows from `LatticePointCount.proof`.
-/
theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.proof

/- English proof (translation)
The claim follows from `BoundedMonomials.proof`.
-/
theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.proof

/- English proof (translation)
The claim follows from `SectionSmall.proof`.
-/
theorem SectionSmall.full : SectionSmall.Statement :=
  SectionSmall.proof

/- English proof (translation)
The claim follows from `DualBasisExists.proof`.
-/
theorem DualBasisExists.full : DualBasisExists.Statement :=
  DualBasisExists.proof

/- English proof (translation)
The claim follows from `OneBlockStandard.proof`.
-/
theorem OneBlockStandard.full : OneBlockStandard.Statement :=
  OneBlockStandard.proof

/- English proof (translation)
The claim follows from `OneBlockPoints.proof`.
-/
theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.proof

/- English proof (translation)
The claim follows from `ChartLatSection.proof`.
-/
theorem ChartLatSection.full : ChartLatSection.Statement :=
  ChartLatSection.proof

/- English proof (translation)
The claim follows from `ChartLatNmSection.proof`.
-/
theorem ChartLatNmSection.full : ChartLatNmSection.Statement :=
  ChartLatNmSection.proof

/- English proof (translation)
The claim follows from `ReadsMul.proof`.
-/
theorem ReadsMul.full : ReadsMul.Statement :=
  ReadsMul.proof

/- English proof (translation)
The claim follows from `YPlusSec.proof`.
-/
theorem YPlusSec.full : YPlusSec.Statement :=
  YPlusSec.proof

/- English proof (translation)
The claim follows from `LineIdealDual.proof`.
-/
theorem LineIdealDual.full : LineIdealDual.Statement :=
  LineIdealDual.proof

/- English proof (translation)
The claim follows from `IdealIndexPlaces.proof`.
-/
theorem IdealIndexPlaces.full : IdealIndexPlaces.Statement :=
  IdealIndexPlaces.proof

/- English proof (translation)
The claim follows from `ConePoints.proof ChartVanishing.full`.
-/
theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.proof ChartVanishing.full

/- English proof (translation)
The claim follows from `ConePointsConverse.proof ChartVanishing.full`.
-/
theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.proof ChartVanishing.full

/- English proof (translation)
The claim follows from `ChartDenominatorAlt.proof ChartVanishing.full`.
-/
theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.proof ChartVanishing.full

/- English proof (translation)
The claim follows from `ChartMetric.proof ChartDenominatorAlt.full ConePoints.full ChartCrossRatio.full`.
-/
theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.proof ChartDenominatorAlt.full ConePoints.full ChartCrossRatio.full

/- English proof (translation)
The claim follows from `PlurisubharmonicMetric.proof ConePoints.full ChartMetric.full`.
-/
theorem PlurisubharmonicMetric.full : PlurisubharmonicMetric.Statement :=
  PlurisubharmonicMetric.proof ConePoints.full ChartMetric.full

/- English proof (translation)
The claim follows from `SectionNorm.proof ConePoints.full ChartMetric.full`.
-/
theorem SectionNorm.full : SectionNorm.Statement :=
  SectionNorm.proof ConePoints.full ChartMetric.full

/- English proof (translation)
The claim follows from `SmallSections.proof ChartFormsAlt.full`.
-/
theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.proof ChartFormsAlt.full

/- English proof (translation)
The claim follows from `SupNormEquality.proof BlockSurjectivity.full`.
-/
theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.proof BlockSurjectivity.full

/- English proof (translation)
The claim follows from `BlockImage.proof IntDomainDim.full ConeTrdeg.full`.
-/
theorem BlockImage.full : BlockImage.Statement :=
  BlockImage.proof IntDomainDim.full ConeTrdeg.full

/- English proof (translation)
The claim follows from `GeometricArithmeticNumbers.proof WeightedDegree.full FibreCompDimZ.full`.
-/
theorem GeometricArithmeticNumbers.full : GeometricArithmeticNumbers.Statement :=
  GeometricArithmeticNumbers.proof WeightedDegree.full FibreCompDimZ.full

/- English proof (translation)
The claim follows from `FibrePoints.proof GeometricArithmeticNumbers.full`.
-/
theorem FibrePoints.full : FibrePoints.Statement :=
  FibrePoints.proof GeometricArithmeticNumbers.full

/- English proof (translation)
The claim follows from `LatticeLineExists.proof OneBlockPoints.full`.
-/
theorem LatticeLineExists.full : LatticeLineExists.Statement :=
  LatticeLineExists.proof OneBlockPoints.full

/- English proof (translation)
The claim follows from `PointHeightDegree.proof OneBlockPoints.full LatticeLineExists.full LineIdealDual.full IdealIndexPlaces.full`.
-/
theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.proof OneBlockPoints.full LatticeLineExists.full LineIdealDual.full IdealIndexPlaces.full

/- English proof (translation)
The claim follows from `AddBlockBridge.proof ChartLatSection.full`.
-/
theorem AddBlockBridge.full : AddBlockBridge.Statement :=
  AddBlockBridge.proof ChartLatSection.full

/- English proof (translation)
The claim follows from `YPlusArithVar.proof ChartPrimality.full ExtensionDimension.full`.
-/
theorem YPlusArithVar.full : YPlusArithVar.Statement :=
  YPlusArithVar.proof ChartPrimality.full ExtensionDimension.full

/- English proof (translation)
The claim follows from `YPlusMetric.proof ChartFormsAlt.full HomogGeneratorsExist.full ChartMetric.full ConePoints.full`.
-/
theorem YPlusMetric.full : YPlusMetric.Statement :=
  YPlusMetric.proof ChartFormsAlt.full HomogGeneratorsExist.full ChartMetric.full ConePoints.full

/- English proof (translation)
The claim follows from `YPlusSmall.proof ChartFormsAlt.full ConePointsConverse.full`.
-/
theorem YPlusSmall.full : YPlusSmall.Statement :=
  YPlusSmall.proof ChartFormsAlt.full ConePointsConverse.full

/- English proof (translation)
The claim follows from `YPlusSupSmall.proof ChartFormsAlt.full ConePoints.full`.
-/
theorem YPlusSupSmall.full : YPlusSupSmall.Statement :=
  YPlusSupSmall.proof ChartFormsAlt.full ConePoints.full

/- English proof (translation)
The claim follows from `OneBlockModel.proof (CoordConeArithVar.proof IntDomainDim.full)`.
-/
theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.proof (CoordConeArithVar.proof IntDomainDim.full)

end GroundTheory.Heights₂.Heights

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

/- English proof (translation)
The claim follows from `WeightedDegree.equiv.mp GroundTheory.Heights₂.Heights.WeightedDegree.full`.
-/
theorem WeightedDegree.full : WeightedDegree.Statement :=
  WeightedDegree.equiv.mp GroundTheory.Heights₂.Heights.WeightedDegree.full

/- English proof (translation)
The claim follows from `BoundedMonomials.equiv.mp GroundTheory.Heights₂.Heights.BoundedMonomials.full`.
-/
theorem BoundedMonomials.full : BoundedMonomials.Statement :=
  BoundedMonomials.equiv.mp GroundTheory.Heights₂.Heights.BoundedMonomials.full

/- English proof (translation)
The claim follows from `HadamardGramBound.equiv.mp GroundTheory.Heights₂.Heights.HadamardGramBound.full`.
-/
theorem HadamardGramBound.full : HadamardGramBound.Statement :=
  HadamardGramBound.equiv.mp GroundTheory.Heights₂.Heights.HadamardGramBound.full

/- English proof (translation)
The claim follows from `MonomialMap.equiv.mp GroundTheory.Heights₂.Heights.MonomialMap.full`.
-/
theorem MonomialMap.full : MonomialMap.Statement :=
  MonomialMap.equiv.mp GroundTheory.Heights₂.Heights.MonomialMap.full

/- English proof (translation)
The claim follows from `OneBlockPoints.equiv.mp GroundTheory.Heights₂.Heights.OneBlockPoints.full`.
-/
theorem OneBlockPoints.full : OneBlockPoints.Statement :=
  OneBlockPoints.equiv.mp GroundTheory.Heights₂.Heights.OneBlockPoints.full

/- English proof (translation)
The claim follows from `ChartRingDescription.equiv.mp GroundTheory.Heights₂.Heights.ChartRingDescription.full`.
-/
theorem ChartRingDescription.full : ChartRingDescription.Statement :=
  ChartRingDescription.equiv.mp GroundTheory.Heights₂.Heights.ChartRingDescription.full

/- English proof (translation)
The claim follows from `ChartCrossRatio.equiv.mp GroundTheory.Heights₂.Heights.ChartCrossRatio.full`.
-/
theorem ChartCrossRatio.full : ChartCrossRatio.Statement :=
  ChartCrossRatio.equiv.mp GroundTheory.Heights₂.Heights.ChartCrossRatio.full

/- English proof (translation)
The claim follows from `ChartDenominatorAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartDenominatorAlt.full`.
-/
theorem ChartDenominatorAlt.full : ChartDenominatorAlt.Statement :=
  ChartDenominatorAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartDenominatorAlt.full

/- English proof (translation)
The claim follows from `ExtensionDimension.equiv.mp GroundTheory.Heights₂.Heights.ExtensionDimension.full`.
-/
theorem ExtensionDimension.full : ExtensionDimension.Statement :=
  ExtensionDimension.equiv.mp GroundTheory.Heights₂.Heights.ExtensionDimension.full

/- English proof (translation)
The claim follows from `ChartFormsAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartFormsAlt.full`.
-/
theorem ChartFormsAlt.full : ChartFormsAlt.Statement :=
  ChartFormsAlt.equiv.mp GroundTheory.Heights₂.Heights.ChartFormsAlt.full

/- English proof (translation)
The claim follows from `ChartMetric.equiv.mp GroundTheory.Heights₂.Heights.ChartMetric.full`.
-/
theorem ChartMetric.full : ChartMetric.Statement :=
  ChartMetric.equiv.mp GroundTheory.Heights₂.Heights.ChartMetric.full

/- English proof (translation)
The claim follows from `ConePointsConverse.equiv.mp GroundTheory.Heights₂.Heights.ConePointsConverse.full`.
-/
theorem ConePointsConverse.full : ConePointsConverse.Statement :=
  ConePointsConverse.equiv.mp GroundTheory.Heights₂.Heights.ConePointsConverse.full

/- English proof (translation)
The claim follows from `ConePoints.equiv.mp GroundTheory.Heights₂.Heights.ConePoints.full`.
-/
theorem ConePoints.full : ConePoints.Statement :=
  ConePoints.equiv.mp GroundTheory.Heights₂.Heights.ConePoints.full

/- English proof (translation)
The claim follows from `ChartPrimality.equiv.mp GroundTheory.Heights₂.Heights.ChartPrimality.full`.
-/
theorem ChartPrimality.full : ChartPrimality.Statement :=
  ChartPrimality.equiv.mp GroundTheory.Heights₂.Heights.ChartPrimality.full

/- English proof (translation)
The claim follows from `SectionCycle.equiv.mp GroundTheory.Heights₂.Heights.SectionCycle.full`.
-/
theorem SectionCycle.full : SectionCycle.Statement :=
  SectionCycle.equiv.mp GroundTheory.Heights₂.Heights.SectionCycle.full

/- English proof (translation)
The claim follows from `SmallSections.equiv.mp GroundTheory.Heights₂.Heights.SmallSections.full`.
-/
theorem SmallSections.full : SmallSections.Statement :=
  SmallSections.equiv.mp GroundTheory.Heights₂.Heights.SmallSections.full

/- English proof (translation)
The claim follows from `ChartVanishing.equiv.mp GroundTheory.Heights₂.Heights.ChartVanishing.full`.
-/
theorem ChartVanishing.full : ChartVanishing.Statement :=
  ChartVanishing.equiv.mp GroundTheory.Heights₂.Heights.ChartVanishing.full

/- English proof (translation)
The claim follows from `BlockSurjectivity.equiv.mp GroundTheory.Heights₂.Heights.BlockSurjectivity.full`.
-/
theorem BlockSurjectivity.full : BlockSurjectivity.Statement :=
  BlockSurjectivity.equiv.mp GroundTheory.Heights₂.Heights.BlockSurjectivity.full

/- English proof (translation)
The claim follows from `SupNormEquality.equiv.mp GroundTheory.Heights₂.Heights.SupNormEquality.full`.
-/
theorem SupNormEquality.full : SupNormEquality.Statement :=
  SupNormEquality.equiv.mp GroundTheory.Heights₂.Heights.SupNormEquality.full

/- English proof (translation)
The claim follows from `SectionInjectivity.equiv.mp GroundTheory.Heights₂.Heights.SectionInjectivity.full`.
-/
theorem SectionInjectivity.full : SectionInjectivity.Statement :=
  SectionInjectivity.equiv.mp GroundTheory.Heights₂.Heights.SectionInjectivity.full

/- English proof (translation)
The claim follows from `LatticePacking.equiv.mp GroundTheory.Heights₂.Heights.LatticePacking.full`.
-/
theorem LatticePacking.full : LatticePacking.Statement :=
  LatticePacking.equiv.mp GroundTheory.Heights₂.Heights.LatticePacking.full

/- English proof (translation)
The claim follows from `(SectionNorm.equiv GroundTheory.Heights₂.Heights.ChartMetric.full).mp GroundTheory.Heights₂.Heights.SectionNorm.full`.
-/
theorem SectionNorm.full : SectionNorm.Statement :=
  (SectionNorm.equiv GroundTheory.Heights₂.Heights.ChartMetric.full).mp GroundTheory.Heights₂.Heights.SectionNorm.full

/- English proof (translation)
The claim follows from `LatticePointCount.hilbDegreeBound_alt_of_statement GroundTheory.Heights₂.Heights.LatticePointCount.full`.
-/
theorem LatticePointCount.full : LatticePointCount.Statement :=
  LatticePointCount.hilbDegreeBound_alt_of_statement GroundTheory.Heights₂.Heights.LatticePointCount.full

/- English proof (translation)
The claim follows from `OneBlockModel.imp GroundTheory.Heights₂.Heights.OneBlockModel.full`.
-/
theorem OneBlockModel.full : OneBlockModel.Statement :=
  OneBlockModel.imp GroundTheory.Heights₂.Heights.OneBlockModel.full

/- English proof (translation)
The claim follows from `LineDegreeBundle.proof`.
-/
theorem LineDegreeBundle.full : LineDegreeBundle.Statement :=
  LineDegreeBundle.proof

/- English proof (translation)
The claim follows from `PointHeightDegree.forward LineDegreeBundle.full GroundTheory.Heights₂.Heights.PointHeightDegree.full`.
-/
theorem PointHeightDegree.full : PointHeightDegree.Statement :=
  PointHeightDegree.forward LineDegreeBundle.full GroundTheory.Heights₂.Heights.PointHeightDegree.full

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
