import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeCollarMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepWeightMass
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PLocalizedQuotientLength
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResNullForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensChartSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanDensIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBergmanIntegrable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBetaSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalCoordinates
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHeightsirationalHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockChiCovolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphFibreRatio
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageMetrics
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockMeasureChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartTaylorCover
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexTaylorTwo
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConjIntNum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCovolumeLeGram
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDoubleComplexVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRelLift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegMatAct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenFibreHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedVOfGeneratedMod
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedEffectiveSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedMixedNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedNonzeroSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedOne
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedPow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedProductNonneg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGeneratedRestrict
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibre
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenericFibreVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramChiDerivative
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGramContraction
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGraphIsometricForms
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SaturatedSaturation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHalving
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbFnValueSpan
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertModule
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneRegularSection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntNumComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralAgainstPositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntegralOfBergman
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLatticeCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftSpread
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocalRep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLogDetDerivative
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricTransportSmooth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMinkowskiCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedTopAlgebra
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPacking
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonnegAtZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolySandwich
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolydiscSubmean
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameBasePtFree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibreDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtRel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtTransc
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatNoetherFrame
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatioFieldDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionComplex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelChartPoly
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelOneStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRelTorsionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionFormsIndependent
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionImageSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionInterpIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionMetricPair
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionPullback
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResolutionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PScaledFSHProps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecCochReduce
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBoundedMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionProduct
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionSupBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiposTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGen
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftIntersectionPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallBallVolume
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanningExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSublatticeExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LerpSelfZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundCount
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTopConstantTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTranscRatioDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCoeffCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCycleExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockHorizDiv
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockStepBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUniformBergmanBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphImage
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseResolution
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.DetRestrictScalarsEqZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockGenFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartRankAdjoin
import GroundTheory.HeightsAndTheta.Heights.Intersections.PFibreIsolFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import GroundTheory.HeightsAndTheta.Heights.Intersections.PHorizNotMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingNoeth
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
import GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTer
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.SpanSingletonEqRangeLsmul
import GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIsSheetFinZero
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRegCurvBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSheetHessPSD
import GroundTheory.HeightsAndTheta.Heights.Intersections.PSwapCycles
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.BergmanLerpSelf
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PProjDegGenDeg
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.MoriwakiHSFull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreDegreeSum
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreCoordGoodProj
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegrePartition
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NoetherProjection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootsLiftToZeros.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FiniteSeparatingModel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof NoetherProjection.full RootsLiftToZeros.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootsNear.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootsBounded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolyNonvanishDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RatPrimeDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof FiniteSeparatingModel.full RootsNear.full RootsBounded.full PolyNonvanishDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NonvanishingDense.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof RatPrimeDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AnResNullForm.full : GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.AnResNullForm.proof NonvanishingDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BergmanDensChartSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensChartSum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BergmanDensIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanDensIntegrable.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BergmanIntegrable.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BergmanIntegrable.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BetaSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BetaSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BetaSum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BirationalCoordinates.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalCoordinates.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BirationalModelExists.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BirationalModelExists.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbFnValueSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbFnValueSpan.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockBirationalHilbert.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockBirationalHilbert.proof HilbFnValueSpan.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockChiCovolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockChiCovolume.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockGraphFibreRatio.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphFibreRatio.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockGraphImage.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockImageArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageArith.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EventualPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolynomial.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultigradedHilbertPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedHilbertPolynomial.proof EventualPolynomial.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenericFibreVar.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibreVar.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.FieldNumbers.HilbEventuallyPoly : GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.HilbEventuallyPoly.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenFibreHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenFibreHomog.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockImageHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageHilb.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolySandwich.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolySandwich.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockImageGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageGenDeg.proof MultigradedHilbertPolynomial.full GenericFibreVar.full Closed.FieldNumbers.HilbEventuallyPoly GenFibreHomog.full BlockImageHilb.full BlockBirationalHilbert.full PolySandwich.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockImageMetrics.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageMetrics.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolydiscSubmean.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolydiscSubmean.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartTaylorCover.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartTaylorCover.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UniformBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.UniformBergmanBound.proof PolydiscSubmean.full ChartTaylorCover.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupNormAgainstL2.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupNormAgainstL2.proof UniformBergmanBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionPullback.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionPullback.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupBoundBlock.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundBlock.proof SupNormAgainstL2.full ResolutionPullback.full NonvanishingDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockMeasureChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockMeasureChange.proof SupBoundBlock.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionFormsIndependent.proof NonvanishingDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionInterpIntegral.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockResolutionMetricPair.proof BergmanDensChartSum.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RankOfSections.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RankOfSections.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.RankOfSections.closed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenericFibre.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenericFibre.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsRank.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlockSectionsRank.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockSectionsRank.proof RankOfSections.full GenericFibre.full SectionsRank.full BlockImageArith.full BlockImageGenDeg.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ComplexTaylorTwo.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexTaylorTwo.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ComplexTaylorTwo.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartBergmanBound.proof PolydiscSubmean.full ComplexTaylorTwo.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartConstantsDetermined.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartDenominator.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartDenominator.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ChartSupBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramChiDerivative.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GramChiDerivative.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MetricChange.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricChange.proof GramChiDerivative.full BergmanIntegrable.full BergmanDensIntegrable.full UniformBergmanBound.full BergmanL1Convergence.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionImageSup.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionImageSup.proof ChartSupBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionSupBound.proof ResolutionImageSup.full NonvanishingDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameBasePtFree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameBasePtFree.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionMetricPair.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionMetricPair.proof BergmanDensChartSum.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionFormsIndependent.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionFormsIndependent.proof NonvanishingDense.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConjIntNum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConstantShift.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConstantsDescend.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConstantsRegular.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof ConstantsDescend.full ChartConstantsDetermined.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoordArithOfFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CovolumeLeGram.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CovolumeLeGram.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CovolumeLeGram.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CurvePointsFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.CurvePointsFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.CurvePointsFinite.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResolutionInterpIntegral.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResolutionInterpIntegral.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegLTGrowth.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DegLTGrowth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DegLTGrowth.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DegreePositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DegreePositive.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DoubleComplexVanish.full : GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.DoubleComplexVanish.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EmbeddingWeight.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EventualPolyLine.full : GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FibreRelLift.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FibreRelLift.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FiltrationHilbSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem G1.full : GroundTheory.Heights₂.Heights.HilbertSamuel.G1.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.G1.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SecEq.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SecEq.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.CondStatement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Conductor.proof SecEq.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelSectionsLarge.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelSectionsLarge.Statement :=
  GroundTheory.Heights₂.Heights.Targets.RelSectionsLarge.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SuccessiveMinimaSpan.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SuccessiveMinimaSpan.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SuccessiveMinimaSpan.of_leaves Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond RelSectionsLarge.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SegrePrime.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegrePrime.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SegreHilb.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreHilb.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SegreDimGe.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SegreDimGe.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultiDegreePositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultiDegreePositive.proof SegrePrime.full SegreHilb.full SegreDimGe.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenDegAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegAmple.proof GenericFibreVar.full MultiDegreePositive.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenDegMatAct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegMatAct.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenOnFibres.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenOnFibres.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedOne.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedOne.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedOne.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedRestrict.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedRestrict.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedEffectiveSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedEffectiveSection.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedProductNonneg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedProductNonneg.proof GeneratedRestrict.full GeneratedEffectiveSection.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedMixedNonneg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedMixedNonneg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedMixedNonneg.proof GeneratedProductNonneg.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenDegTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegTwist.proof GenOnFibres.full GenericFibreVar.full GeneratedOne.full GeneratedMixedNonneg.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem QuotPartGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.QuotPartGraded.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenerationOfH1GenAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenerationOfH1GenAmple.proof QuotPartGraded.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GenTwistGenerated.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedNonzeroSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedNonzeroSection.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GeneratedPow.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GeneratedPow.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GradedSubquot.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GradedSubquot.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramContraction.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GramContraction.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GramContraction.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GraphIsometric.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometric.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GraphIsometricForms.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GraphIsometricForms.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GridSum.full : GroundTheory.Heights₂.Heights.HilbertSamuel.GridSum.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.GridSum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Had.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Had.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Had.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Halving.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Halving.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Halving.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbertDimZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertDimZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertDimZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntersectionRecursion.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntersectionRecursion.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntersectionRecursion.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbertIncrement.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement.proof IntersectionRecursion.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MultigradedFiltration.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ModulesFromPrimes.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ModulesFromPrimes.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ModulesFromPrimes.proof MultigradedFiltration.full FiltrationHilbSum.full DegLTGrowth.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbertPrime.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertPrime.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.hilbertPrime

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HilbertModule.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertModule.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertModule.proof ModulesFromPrimes.full HilbertPrime.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HyperplaneRegularSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.HyperplaneRegularSection.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntNumComponents.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntNumComponents.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntNumComponents.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntegralAgainstPositive.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralAgainstPositive.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IntegralOfBergman.full : GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralOfBergman.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.IntegralOfBergman.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem L1Convergence.full : GroundTheory.Heights₂.Heights.HilbertSamuel.L1Convergence.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.L1Convergence.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem L2GramLattice.full : GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.L2GramLattice.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LatticeCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LatticeCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LiftBirationalAmple.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple.proof GeneratedNonzeroSection.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LiftSpread.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LiftSpread.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalBergmanBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LocalBergmanBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LocalBergmanBound.proof ChartBergmanBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LocalRep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LogDetDerivative.full : GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.LogDetDerivative.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MetricTransportSmooth.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MetricTransportSmooth.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MinkowskiCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MinkowskiCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MixedNumberPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.HilbertPositive.mixedNumber

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolyNonnegAtZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonnegAtZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MixedTopAlgebra.full : GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.MixedTopAlgebra.proof PolyNonnegAtZero.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NefOnGenericOfSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NefOnGenericOfSemipos.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NmSectionsFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NmSectionsRankBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.NmSectionsRankBound.proof NmSectionsFinite.full SecMRankBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Packing.full : GroundTheory.Heights₂.Heights.HilbertSamuel.Packing.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Packing.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PerturbMonomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbMonomial.proof GenDegAmple.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PerturbSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PerturbSemipos.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PointHeightFS.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PointHeightFS.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjDegGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjDegGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ProjDegGenDeg.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameFibrePt.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibrePt.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameGenPtRel.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtRel.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameGenPtTransc.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameGenPtTransc.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TranscRatioDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TranscRatioDeg.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RatioFieldDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatioFieldDeg.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameFibreDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameFibreDeg.proof ProjFrameFibrePt.full ProjFrameGenPtRel.full ProjFrameGenPtTransc.full TranscRatioDeg.full RatioFieldDeg.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProjFrameImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjFrameImage.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RatNoetherFrame.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RatNoetherFrame.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ReductionComplex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ReductionComplex.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelChartPoly.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelChartPoly.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelChartPoly.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelLatticeFinite.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelLatticeFinite.proof RelSectionsLarge.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelTorsionBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelTorsionBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelTorsionBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RelOneStep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RelOneStep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RelOneStep.proof RelChartPoly.full RelTorsionBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ResVolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResVolume.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RootGridLower.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RootGridLower.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RootGridLower.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ScaledFSHProps.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ScaledFSHProps.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SecCochReduce.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SecCochReduce.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionBounded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBounded.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionBoundedMul.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionBoundedMul.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionOrderAtPoint.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionOrderAtPoint.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionPointValue.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionPointValue.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionProduct.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionProduct.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpanStepLocal.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepLocal.proof RelLatticeFinite.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpanStepHomog.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanStepHomog.proof SpanStepLocal.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SerreGraded.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SerreGraded.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionSpanStep.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSpanStep.proof SpanStepHomog.full SerreGraded.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionSupBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionSupBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionsDimZero.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SectionsDimZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SemiampleNef.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SemiampleNef.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SemiampleNef.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SemiposTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SemiposTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SemiposTwist.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ShiftDegreePolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftDegreePolynomial.proof MixedNumberPolynomial.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ShiftIntersectionPolynomial.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ShiftIntersectionPolynomial.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SmallBallVolume.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallBallVolume.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallBallVolume.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SmallGenTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallGenTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallGenTwist.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SmallSectionPointHeight.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionPointHeight.proof SectionOrderAtPoint.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpanningExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SpanningExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SpanningExtension.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SublatticeDegree.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeDegree.Statement :=
  GroundTheory.Heights₂.Heights.Targets.SublatticeDegree.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SublatticeExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SublatticeExtension.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SupBoundCount.full : GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.SupBoundCount.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TopConstantTwist.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwoBlockFnField.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockFnField.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwoBlockHorizDiv.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockHorizDiv.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwoBlockCoeffCycle.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCoeffCycle.proof CoordArithOfFnField.full TwoBlockFnField.full TwoBlockHorizDiv.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwoBlockCycleExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockCycleExpand.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TwoBlockStepBound.full : GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.TwoBlockStepBound.proof RankOfSections.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UnitApprox.full : GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeroneseArith.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseArith.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeroneseGenDeg.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGenDeg.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeroneseGraphImage.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseGraphImage.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeroneseResolution.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseResolution.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VeroneseSemipos.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseSemipos.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZCombExpand.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombExpand.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZCombLimit.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZCombLimit.Statement :=
  GroundTheory.Heights₂.Heights.Swarm.ZCombLimit.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZeroCocycleSection.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ZeroCocycleSection.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.IndefiniteRowSideFullHecke.Inter.ZIntPoint : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.Statement :=
  GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.ZIntPoint.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZero : ReciprocityTheory.ChartRestriction.G.AI.I2.ArithVarZeroStatement :=
  GroundTheory.Heights₂.Heights.Inter.arithVarZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ReciprocityTheory.ChartRestriction.G.Geo.FibreFinite : ReciprocityTheory.ChartRestriction.G.Geo.FibreFiniteStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityPointsSum_holds : GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityEmbedding_holds : GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.FieldNumbers.LocalizedQuotientLength : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement :=
  GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityLocalFlat_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityDehomogenization_holds : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.proof Closed.FieldNumbers.LocalizedQuotientLength Closed.Inter.regularityLocalFlat_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.LocRingFrac : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingFrac.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.LocRingLocal : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingLocal.proof Closed.Inter.LocRingFrac

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.LocRingNoeth : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.proof Closed.Inter.LocRingFrac

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.LocRingPow : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingPow.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityLocalDimension_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.proof Closed.Inter.LocRingFrac Closed.Inter.LocRingLocal Closed.Inter.LocRingNoeth Closed.Inter.LocRingPow

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityLocalResidue_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalResidue_holds.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.regularityLocalCardinality_holds : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.proof Closed.Inter.regularityLocalDimension_holds Closed.Inter.regularityLocalResidue_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.PtsSumMeasurable : GroundTheory.Heights₂.Heights.PtsSumMeasurable.Statement :=
  GroundTheory.Heights₂.Heights.PtsSumMeasurable.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.SwapCycles : GroundTheory.Heights₂.Heights.Inter.SwapCycles.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SwapCycles.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.GeoNumCut : GroundTheory.Heights₂.Heights.Inter.GeoNumCut.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.TorusInvLevi : GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.Statement :=
  GroundTheory.Heights₂.Heights.Inter.TorusInvLevi.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.SemiPosTwist : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.proof Closed.Inter.TorusInvLevi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.SegrePartition : GroundTheory.Heights₂.Heights.SegrePartition.Statement :=
  GroundTheory.Heights₂.Heights.SegrePartition.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.SegreChartDim : GroundTheory.Heights₂.Heights.SegreChartDim.Statement :=
  GroundTheory.Heights₂.Heights.SegreChartDim.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.SegreCoordGoodProj : GroundTheory.Heights₂.Heights.SegreCoordGoodProj.Statement :=
  GroundTheory.Heights₂.Heights.SegreCoordGoodProj.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ComplexSets.DiscriminantCover : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement :=
  GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.TubeCollarCompare : GroundTheory.Heights₂.Heights.TubeCollarCompare.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarCompare.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.SheetImageAreaSet : GroundTheory.Heights₂.Heights.SheetImageAreaSet.Statement :=
  GroundTheory.Heights₂.Heights.SheetImageAreaSet.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ChartMassCompare : GroundTheory.Heights₂.Heights.ChartMassCompare.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompare.of_open Closed.SheetImageAreaSet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.MassFinite : GroundTheory.Heights₂.Heights.MassFinite.Statement :=
  GroundTheory.Heights₂.Heights.MassFinite.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.TubeCollarMass : GroundTheory.Heights₂.Heights.TubeCollarMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeCollarMass.proof Closed.TubeCollarCompare Closed.ChartMassCompare Closed.MassFinite

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.TubeDeepWeightMass : GroundTheory.Heights₂.Heights.TubeDeepWeightMass.Statement :=
  GroundTheory.Heights₂.Heights.TubeDeepWeightMass.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ChartMassCompact : GroundTheory.Heights₂.Heights.ChartMassCompact.Statement :=
  GroundTheory.Heights₂.Heights.ChartMassCompact.of_open Closed.SheetImageAreaSet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.CutOffBoundaryBound : GroundTheory.Heights₂.Heights.CutOffBoundaryBound.Statement :=
  GroundTheory.Heights₂.Heights.CutOffBoundaryBound.of_open Closed.SheetImageAreaSet

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.SheetHessPSD : GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.RegCurvBound : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegCurvBound.proof Closed.Inter.TorusInvLevi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.HorizNotMem : GroundTheory.Heights₂.Heights.Inter.HorizNotMem.Statement :=
  GroundTheory.Heights₂.Heights.Inter.HorizNotMem.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.RatioAlgDep : GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RatioAlgDep.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.pointFormRank_holds : GroundTheory.Heights₂.Heights.Inter.pointFormRank_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointFormRank_holds.proof Closed.Inter.RatioAlgDep

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.pointFormEuler_holds : GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.pointForm_holds : GroundTheory.Heights₂.Heights.Inter.pointForm_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pointForm_holds.proof Closed.Inter.pointFormRank_holds Closed.Inter.pointFormEuler_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.PFIntZero : GroundTheory.Heights₂.Heights.Inter.PFIntZero.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PFIntZero.proof Closed.Inter.pointFormRank_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoord : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageCoordStatement :=
  GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.BlockRatioAlg : GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockRatioAlg.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.BlockGenFinite : GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.BlockGenFinite.proof Closed.Inter.BlockRatioAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.FibreIsolFinite : GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreIsolFinite.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.ChartRankAdjoin : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Closed.Inter.pullbackBadImage_holds : GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
