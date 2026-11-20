import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Imports
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.RestAssembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualArithVar
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSmooth
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineLevi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsLineSemipositive
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PNefOfNonneg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PFsConjInvariant
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassLeRoot
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDivSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootAnchorNonzero
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointConj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootPointsFinite
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootLogNormBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPtsIntegralZeroLowerNE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PMultiHomogMemCoord
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootHeightNE
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootDense
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGrassHeightBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLatticeBasisExists
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualEmbBijective
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineSemipositive
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineConj
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointDegCPos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointArInt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPointVertR
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPointLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PTelescope
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopSubLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegStandard
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopMetricChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopLatticeChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopStandard
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualTopBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOfPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMassAt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegPos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLineOfLargeDegreeDual
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
The claim follows from `CoordConeArithVar.proof IntDomainDim.full`.
-/
theorem CoordConeArithVar.full : CoordConeArithVar.Statement :=
  CoordConeArithVar.proof IntDomainDim.full

/- English proof (translation)
The claim follows from `GrassArithVar.proof CoordConeArithVar.full`.
-/
theorem GrassArithVar.full : GrassArithVar.Statement := GrassArithVar.proof CoordConeArithVar.full

/- English proof (translation)
The claim follows from `RootArithVar.proof CoordConeArithVar.full`.
-/
theorem RootArithVar.full : RootArithVar.Statement := RootArithVar.proof CoordConeArithVar.full

/- English proof (translation)
The claim follows from `DualArithVar.proof CoordConeArithVar.full`.
-/
theorem DualArithVar.full : DualArithVar.Statement := DualArithVar.proof CoordConeArithVar.full

/- English proof (translation)
The claim follows from `FsLineSemipositive.proof FsLineSmooth.proof FsLineLevi.proof`.
-/
theorem FsLineSemipositive.full : FsLineSemipositive.Statement :=
  FsLineSemipositive.proof FsLineSmooth.proof FsLineLevi.proof

/- English proof (translation)
The claim follows from `RootPointConj.proof RootAnchorNonzero.proof`.
-/
theorem RootPointConj.full : RootPointConj.Statement := RootPointConj.proof RootAnchorNonzero.proof

/- English proof (translation)
The claim follows from `RootPointsFinite.proof RootAnchorNonzero.proof`.
-/
theorem RootPointsFinite.full : RootPointsFinite.Statement :=
  RootPointsFinite.proof RootAnchorNonzero.proof

/- English proof (translation)
The claim follows from `RootLogNormBound.proof RootAnchorNonzero.proof RootPointConj.full PlueckerKernel.full`.
-/
theorem RootLogNormBound.full : RootLogNormBound.Statement :=
  RootLogNormBound.proof RootAnchorNonzero.proof RootPointConj.full PlueckerKernel.full

/- English proof (translation)
The claim follows from `RootHeight.proofNE RootArithVar.full RootDivSuppEmpty.proof RootLogNormBound.full RootPointsFinite.full PtsIntegralZeroLowerNE.proof MultiHomogMemCoord.proof FsLineSmooth.proof`.
-/
theorem RootHeight.full : RootHeight.Statement :=
  RootHeight.proofNE RootArithVar.full RootDivSuppEmpty.proof RootLogNormBound.full
    RootPointsFinite.full PtsIntegralZeroLowerNE.proof MultiHomogMemCoord.proof FsLineSmooth.proof

/- English proof (translation)
The claim follows from `RootDense.proof MultiHomogMemCoord.proof RootsOfUnityDense.full`.
-/
theorem RootDense.full : RootDense.Statement :=
  RootDense.proof MultiHomogMemCoord.proof RootsOfUnityDense.full

/- English proof (translation)
The claim follows from `GrassHeightBound.proof GrassArithVar.full RootArithVar.full FsLineSemipositive.full NefOfNonneg.proof FsConjInvariant.proof GrassLeRoot.proof RootHeight.full RootDense.full`.
-/
theorem GrassHeightBound.full : GrassHeightBound.Statement :=
  GrassHeightBound.proof GrassArithVar.full RootArithVar.full FsLineSemipositive.full
    NefOfNonneg.proof FsConjInvariant.proof GrassLeRoot.proof RootHeight.full RootDense.full

/- English proof (translation)
The claim follows from `DualStdMassAt.proof DualPtsOnPlane.proof DualPtsOfPlane.proof`.
-/
theorem DualStdMassAt.full : DualStdMassAt.Statement :=
  DualStdMassAt.proof DualPtsOnPlane.proof DualPtsOfPlane.proof

/- English proof (translation)
The claim follows from `DualPointLineDegree.proof DualCurvePoint.proof PointDegCPos.proof PointArInt.proof (PointVertR.proof hVI hSN) DualLineIndex.proof DualLineSemipositive.proof`.
-/
theorem DualPointLineDegree.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement) :
    DualPointLineDegree.Statement :=
  DualPointLineDegree.proof DualCurvePoint.proof PointDegCPos.proof PointArInt.proof
    (PointVertR.proof hVI hSN) DualLineIndex.proof DualLineSemipositive.proof

/- English proof (translation)
The claim follows from `DualTopBound.proof DualLatticeBasisExists.proof DualEmbBijective.proof (DualTopMetricChange.proof Telescope.proof hEnergy) (DualTopLatticeChange.proof (DualTopSubLattice.proof hBasis hStacked hSDeg)) (DualTopStandard.proof hBC hGL) (DualGeomDegStandard.proof hCharts hGChart hMass …`.
-/
theorem DualTopBound.ofOpen (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement) :
    DualTopBound.Statement :=
  DualTopBound.proof DualLatticeBasisExists.proof DualEmbBijective.proof
    (DualTopMetricChange.proof Telescope.proof hEnergy)
    (DualTopLatticeChange.proof (DualTopSubLattice.proof hBasis hStacked hSDeg))
    (DualTopStandard.proof hBC hGL) (DualGeomDegStandard.proof hCharts hGChart hMass)
    GrassHeightBound.full

/- English proof (translation)
The claim follows from `DualGeomDegPos.proof hDeg hInd DualArithVar.full DualLineSemipositive.proof DualPtsOnPlane.proof DualStdMassAt.full`.
-/
theorem DualGeomDegPos.ofOpen (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    DualGeomDegPos.Statement :=
  DualGeomDegPos.proof hDeg hInd DualArithVar.full DualLineSemipositive.proof DualPtsOnPlane.proof
    DualStdMassAt.full

/- English proof (translation)
The claim follows from `LineOfLargeDegreeFromZ.proofDual DualLatticeBasisExists.proof DualEmbBijective.proof DualArithVar.full DualLineSemipositive.proof NefOfNonneg.proof DualLineConj.proof (DualPointLineDegree.ofOpen hVI hSN) (DualTopBound.ofOpen hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart h …`.
-/
theorem LineOfLargeDegreeFromZ.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    LineOfLargeDegreeFromZ.Statement :=
  LineOfLargeDegreeFromZ.proofDual DualLatticeBasisExists.proof DualEmbBijective.proof
    DualArithVar.full DualLineSemipositive.proof NefOfNonneg.proof DualLineConj.proof
    (DualPointLineDegree.ofOpen hVI hSN)
    (DualTopBound.ofOpen hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass)
    (DualGeomDegPos.ofOpen hDeg hInd)

/- English proof (translation)
The claim follows from `KernelsCut.proof (LineOfLargeDegreeFromZ.ofOpen hVI hSN hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass hDeg hInd hZ1 hZ2 hI) (RestTermSharp.ofRestTerms h₁ h₂ h₃ h₄ h₅)`.
-/
theorem KernelsCut.ofOpen (hZ1 : SuccessiveMinimaLowerBound) (hZ2 : SuccessiveMinimaUpperBound)
    (hI : ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement)
    (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement)
    (h₁ : RestTerms.CoinvariantTopDegree.Statement)
    (h₂ : RestTerms.FlagIntegralKillsPowerSums.Statement)
    (h₃ : RestTerms.RestTermWellDefined.Statement) (h₄ : RestTerms.SameFactorBound.Statement)
    (h₅ : RestTerms.RestBound.Statement) : KernelsCut.Statement :=
  KernelsCut.proof
    (LineOfLargeDegreeFromZ.ofOpen hVI hSN hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart
      hMass hDeg hInd hZ1 hZ2 hI)
    (RestTermSharp.ofRestTerms h₁ h₂ h₃ h₄ h₅)

end GroundTheory.Heights₂.Heights
