import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafLocalizationOfInjectiveSliceOfRestrictionInj
import Development.AutomorphicArithmetic.CommutativeAlgebra.CurvePicardOfSelmerPicardOfModelCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.CurveEtaleDescent
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafH0Holds
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafCurveOfLeafH0
import Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureFiniteOfFiniteTypeDomain
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyDegreeZeroSurjectiveLimit
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyClassKilledOnNeighborhood
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveCohomologyKilledByFiniteCover
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleStalkCohomologyStrictHenselianContinuity
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RestrictionInjectiveOfAcyclic
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GeometricFibreCohomologyConstant
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TwistedSectionsOfNegativeDegreeVanishing
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.IsOpenImmersionInclusionOfPiecewise
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FreeEtaleSheafLiftExists
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackIsLimitOverFgSubalgebras
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SepClosedPointFilteredEtaleColimit
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExtensionByZeroOfZariskiQuasiFiniteFactorization
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.DescentMapFactorsThroughStage
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StrictlyHenselianLocalOfNegligibleDegree
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProperGluingExistence
import Development.EtaleCohomology.EtaleSheaves.LeafBaseChangeFieldPf
import Development.EtaleCohomology.EtaleSheaves.LeafBdryPf
import Development.EtaleCohomology.EtaleSheaves.LeafCloseBCut
import Development.EtaleCohomology.EtaleSheaves.LeafClosedImmSpreadPf
import Development.EtaleCohomology.EtaleSheaves.LeafClosedPf
import Development.EtaleCohomology.EtaleSheaves.LeafClosedSH0Of
import Development.EtaleCohomology.EtaleSheaves.LeafClosedSHPosPf
import Development.EtaleCohomology.EtaleSheaves.LeafCompGeomPf
import Development.EtaleCohomology.EtaleSheaves.LeafCompPf
import Development.EtaleCohomology.EtaleSheaves.DiagonalComparison
import Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
import Development.EtaleCohomology.EtaleSheaves.LeafCoprodPf
import Development.EtaleCohomology.EtaleSheaves.CurveKrullDim
import Development.EtaleCohomology.EtaleSheaves.LeafCurveVCut
import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
import Development.EtaleCohomology.EtaleSheaves.DiagramDescent
import Development.EtaleCohomology.EtaleSheaves.LeafReducedSmooth
import Development.EtaleCohomology.EtaleSheaves.LeafDimBoundPf
import Development.EtaleCohomology.EtaleSheaves.LeafDimOpenPf
import Development.EtaleCohomology.EtaleSheaves.LeafExtendCut
import Development.EtaleCohomology.EtaleSheaves.LeafFibreFieldPf
import Development.EtaleCohomology.EtaleSheaves.LeafFiltPf
import Development.EtaleCohomology.EtaleSheaves.DegreeZeroGenerators
import Development.EtaleCohomology.EtaleSheaves.LeafGeoCut
import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
import Development.EtaleCohomology.EtaleSheaves.LeafGhostCut
import Development.EtaleCohomology.EtaleSheaves.LeafGhostRelCut
import Development.EtaleCohomology.EtaleSheaves.LeafGlueDimPf
import Development.EtaleCohomology.EtaleSheaves.GluingExistence
import Development.EtaleCohomology.EtaleSheaves.LeafGlueExtendPf
import Development.EtaleCohomology.EtaleSheaves.LeafGlueGenericPf
import Development.EtaleCohomology.EtaleSheaves.LeafGlueIsProperPf
import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
import Development.EtaleCohomology.EtaleSheaves.GluedCurveChartOverlapIsPullback
import Development.EtaleCohomology.EtaleSheaves.LeafGlueTwoPfQS
import Development.EtaleCohomology.EtaleSheaves.BoundaryKernel
import Development.EtaleCohomology.EtaleSheaves.H0Lifting
import Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
import Development.EtaleCohomology.EtaleSheaves.LeafInj0Of
import Development.EtaleCohomology.EtaleSheaves.RelativeCohomologyForgetInjectiveDegreeZeroOfSub
import Development.EtaleCohomology.EtaleSheaves.EtaleStandingHypothesesImplyRestrictionAxiom
import Development.EtaleCohomology.EtaleSheaves.LeafIntClosureAlgPf
import Development.EtaleCohomology.EtaleSheaves.LeafIrredPf
import Development.EtaleCohomology.EtaleSheaves.RTEqZeroOfPtA
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
import Development.EtaleCohomology.EtaleSheaves.LeafKillCut
import Development.EtaleCohomology.EtaleSheaves.LeafKumCut
import Development.EtaleCohomology.EtaleSheaves.KummerFields
import Development.EtaleCohomology.EtaleSheaves.LeafLiftNonconstOf
import Development.EtaleCohomology.EtaleSheaves.LeafLimFPPf
import Development.EtaleCohomology.EtaleSheaves.LeafLocalExtendPf
import Development.EtaleCohomology.EtaleSheaves.LeafModelCurveCut
import Development.EtaleCohomology.EtaleSheaves.LeafNSysGlueOf
import Development.EtaleCohomology.EtaleSheaves.LeafNegPf
import Development.EtaleCohomology.EtaleSheaves.LeafNormalModelPf
import Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
import Development.EtaleCohomology.EtaleSheaves.OpenSpreadingOut
import Development.EtaleCohomology.EtaleSheaves.LeafProjModelPfImm
import Development.EtaleCohomology.EtaleSheaves.LeafPtPf
import Development.EtaleCohomology.EtaleSheaves.LeafPtVPf
import Development.EtaleCohomology.EtaleSheaves.PointEvaluationWitness
import Development.EtaleCohomology.EtaleSheaves.LeafQCQSInductPf
import Development.EtaleCohomology.EtaleSheaves.QuasiFiniteAtOfIsOpenFiber
import Development.EtaleCohomology.EtaleSheaves.QuotientFieldNonconstantLift
import Development.EtaleCohomology.EtaleSheaves.ReducedOfSmooth
import Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
import Development.EtaleCohomology.EtaleSheaves.LeafRepCut
import Development.EtaleCohomology.EtaleSheaves.StrictHenselianLocalization
import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSysOf
import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys
import Development.EtaleCohomology.EtaleSheaves.LeafSHPtOf
import Development.EtaleCohomology.EtaleSheaves.LeafSHSievePf
import Development.EtaleCohomology.EtaleSheaves.LeafSHSysPf
import Development.EtaleCohomology.EtaleSheaves.LeafSSCut
import Development.EtaleCohomology.EtaleSheaves.LeafSecRepPf
import Development.EtaleCohomology.EtaleSheaves.LeafSelPicPf
import Development.EtaleCohomology.EtaleSheaves.SheafIsomorphism.LeafShIsoOf
import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.LeafShMapZeroOf
import Development.EtaleCohomology.EtaleSheaves.LeafSmoothOfNormalPf
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFGraphOf
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFMapVtuPfG
import Development.EtaleCohomology.EtaleSheaves.SpreadingOutQuasiFinitenessBaseChange
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadRelDimPf
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSeparatedPf
import Development.EtaleCohomology.EtaleSheaves.LeafSpreadSmooth1Of
import Development.EtaleCohomology.EtaleSheaves.LeafStalkOfAlgOf
import Development.EtaleCohomology.EtaleSheaves.LeafStalkSmoothClosedPf
import Development.EtaleCohomology.EtaleSheaves.LeafStalkValuationPf
import Development.EtaleCohomology.EtaleSheaves.CovOfPoints
import Development.EtaleCohomology.EtaleSheaves.ResZeroOfRange
import Development.EtaleCohomology.EtaleSheaves.LeafTermsPf
import Development.EtaleCohomology.EtaleSheaves.LeafTrdegDimPf
import Development.EtaleCohomology.EtaleSheaves.LeafTruncPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwistIsoPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwistPf
import Development.EtaleCohomology.EtaleSheaves.CurveUnitsOrderAtInfinity
import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk
import Development.EtaleCohomology.EtaleSheaves.LeafVanBPf
import Development.EtaleCohomology.EtaleSheaves.LeafVanBStalkPf
import Development.EtaleCohomology.EtaleSheaves.StalkVanishing
import Development.EtaleCohomology.EtaleSheaves.LeafVanVPf
import Development.EtaleCohomology.EtaleSheaves.LeafVanWPf
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.EtaleCohomology.KummerTheory.FinInjSlice

namespace UpperTheory.Et.EtaleTopology

variable (hB6 : GlobalTheory.EtC.DivisorPicardCompatibility)
include hB6

/- English proof (translation)
Establish `a0 : LateralTheory.E.E4.H0TwistOverClosedField` using `UpperTheory.leafH0_holds`. Establish `a1 : LateralTheory.E.E4.LeafPt` using `LateralTheory.E.E4.LeafPt_of a0`. Establish `a2 : LateralTheory.E.E4.LeafCoprod` using `LateralTheory.E.LeafCoprodPf.LeafCoprod_of`. Establish `a3 : LateralTheory.E.E4.LeafCompGeom` using `LateralTheory.E.E4.leafCompGeom`. Establish `a4 : LateralTheory.E.E4.LeafComp` using `LateralTheory.E.E4.LeafComp_of a2 a3`.

Establish `a5 : LateralTheory.E.E4.LeafDesc` using `UpperTheory.curve_etale_descent`. Establish `a6 : LateralTheory.E.LeafSSCut.LeafFilt` using `LateralTheory.E.LeafFiltPf.LeafFilt_of`. Establish `a7 : LateralTheory.E.LeafSSCut.LeafCompare` using `LateralTheory.E.DiagonalComparison.LeafCompare_of`. Establish `a8 : LateralTheory.E.LeafSSCut.LeafTerms` using `LateralTheory.E.LeafTermsPf.LeafTerms_of`. Establish `a9 : LateralTheory.E.E4.LeafSS` using `LateralTheory.E.LeafSSCut.goal_of a6 a7 a8`.

Establish `a10 : LateralTheory.E.E4.LeafUnits` using `LateralTheory.E.CurveUnitsOrderAtInfinity.LeafUnits_of`. Establish `a11 : LateralTheory.E.LeafPicCut.LeafSelPic` using `LateralTheory.E.LeafSelPicPf.LeafSelPic_of`. Establish `a12 : LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite` using `UpperTheory.integralClosure_finite_of_finiteType_domain`. Establish `a13 : LateralTheory.E.LeafNormalModelPf.LeafIntClosureAlg` using `LateralTheory.E.LeafIntClosureAlgPf.LeafIntClosureAlg_of a12`. Establish `a14 : LateralTheory.E.LeafGlueProperPf.LeafGlueExists` using `LateralTheory.E.GluingExistence.LeafGlueExists_of`.

Establish `a15 : LateralTheory.E.LeafGlueProperPf.LeafGlueIntegral` using `LateralTheory.E.LeafGlueProperPf.glued_affine_curve_is_integral_scheme`. Establish `a16 : LateralTheory.E.LeafGlueProperPf.LeafGlueNormal` using `LateralTheory.E.LeafGlueProperPf.glued_affine_curve_stalks_integrally_closed`. Establish `a17 : LateralTheory.E.LeafGlueProperPf.LeafGlueDim` using `LateralTheory.E.LeafGlueDimPf.LeafGlueDim_of`. Establish `a18 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep` using `LateralTheory.E.GluedCurveSeparated.LeafGlueSep_of`. Establish `a19 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence` using `UpperTheory.Cb.properGluing_existence`.

Establish `a20 : LateralTheory.E.LeafGlueProperPf.LeafGlueIsProper` using `LateralTheory.E.LeafGlueIsProperPf.LeafGlueIsProper_of a18 a19`. Establish `a21 : LateralTheory.E.LeafGlueProperPf.LeafGlueGeneric` using `LateralTheory.E.LeafGlueGenericPf.glued_curve_generic_point_maps_to_function_field`. Establish `a22 : LateralTheory.E.LeafNormalModelPf.LeafGlueProper` using `LateralTheory.E.LeafGlueProperPf.LeafGlueProper_of a14 a15 a16 a17 a20 a21`. Establish `a23 : LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel` using `LateralTheory.E.LeafNormalModelPf.LeafNormalModel_of a13 a22`. Establish `a24 : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed` using `LateralTheory.E.LeafStalkSmoothClosedPf.LeafStalkSmoothClosed_of`.

Establish `a25 : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne` using `LateralTheory.E.LeafRelDimOnePf.LeafRelDimOne_of`. Establish `a26 : LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal` using `LateralTheory.E.LeafSmoothOfNormalPf.LeafSmoothOfNormal_of a24 a25`. Establish `a27 : LateralTheory.E.LeafCurveVCut.LeafModelCurve` using `LateralTheory.E.LeafModelCurveCut.goal_of a23 a26`. Establish `a28 : LateralTheory.E.E4.LeafPic` using `UpperTheory.curve_picard_of_selmerPicard_of_modelCurve a11 a27`. Establish `a29 : LateralTheory.E.LeafTwistPf.LeafLoc` using `LateralTheory.E.LeafTwistIsoPf.leafLoc`.

Establish `a30 : LateralTheory.E.LeafTwistPf.LeafTwSec` using `LateralTheory.E.LeafTwistIsoPf.leafTwSec`. Establish `a31 : LateralTheory.E.LeafKumCut.LeafTwist` using `LateralTheory.E.LeafTwistPf.LeafTwist_of a29 a30`. Establish `a32 : LateralTheory.E.LeafKumCut.EtaleFirstCohomologyMultiplicativeGroupPicard` using `(fun _ => hB6)`. Establish `a33 : LateralTheory.E.LeafKumCut.LeafKumSeq` using `LateralTheory.E.LeafKumFieldPf.kumSeq`. Establish `a34 : LateralTheory.E.E4.LeafKum` using `LateralTheory.E.LeafKumCut.goal_of a31 a32 a33`.

Establish `a35 : LateralTheory.E.E4.LeafCurve` using `UpperTheory.leafCurve_of_leafH0 a0`. Establish `a36 : LateralTheory.E.LeafKillCut.LeafOne` using `UpperTheory.Cb.curve_cohomology_killed_by_finite_cover a0`. Establish `a37 : LateralTheory.E.E4.LeafKill` using `LateralTheory.E.LeafKillCut.goal_of a36`. Establish `a38 : LateralTheory.E.LeafCurveVCut.LeafFibreField` using `LateralTheory.E.LeafFibreFieldPf.LeafFibreField_of`. Establish `a39 : LateralTheory.E.LeafCurveVCut.LeafTrdegDim` using `LateralTheory.E.LeafTrdegDimPf.LeafTrdegDim_of`.

Establish `a40 : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField` using `LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of`. Establish `a41 : LateralTheory.E.LeafExtendCut.LeafStalkValuation` using `LateralTheory.E.LeafStalkValuationPf.LeafStalkValuation_of`. Establish `a42 : LateralTheory.E.LeafExtendCut.LeafLocalExtend` using `LateralTheory.E.LeafLocalExtendPf.LeafLocalExtend_of`. Establish `a43 : LateralTheory.E.LeafExtendCut.LeafGlueExtend` using `LateralTheory.E.LeafGlueExtendPf.LeafGlueExtend_of`. Establish `a44 : LateralTheory.E.LeafCurveVCut.LeafExtend` using `LateralTheory.E.LeafExtendCut.goal_of a41 a42 a43`.

Establish `a45 : LateralTheory.E.LeafGeoVCut.LeafCurveV` using `LateralTheory.E.LeafCurveVCut.goal_of a38 a39 a40 a27 a44`. Establish `a46 : LateralTheory.E.LeafDescendVCut.LeafDimBound` using `LateralTheory.E.LeafDimBoundPf.LeafDimBound_of`. Establish `a47 : LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall` using `LateralTheory.E.CurveKrullDim.LeafCurveSmall_of a46`. Establish `a48 : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst` using `LateralTheory.E.NonconstantLift.LeafLiftNonconst_of`. Establish `a49 : LateralTheory.E.QuasiFiniteDescent.LeafQFOmega` using `LateralTheory.E.QuotientFieldNonconstantLift.LeafQFOmega_of a47 a48`.

Establish `a50 : LateralTheory.E.LeafObjFPPf.LeafObjAff` using `LateralTheory.E.LeafObjAffPf.LeafObjAff_of`. Establish `a51 : LateralTheory.E.LeafObjGluePf.LeafGlueTwo` using `LateralTheory.E.LeafGlueTwoPfQS.LeafGlueTwo_of`. Establish `a52 : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct` using `LateralTheory.E.LeafQCQSInductPf.LeafQCQSInduct_of`. Establish `a53 : LateralTheory.E.LeafInclPiecePf.LeafInclMap` using `UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras`. Establish `a54 : LateralTheory.E.LeafInclPiecePf.LeafInclOpen` using `UpperTheory.Cb.isOpenImmersion_inclusion_of_piecewise`.

Establish `a55 : LateralTheory.E.LeafInclDescendPf.LeafInclPiece` using `LateralTheory.E.LeafInclPiecePf.LeafInclPiece_of a53 a54`. Establish `a56 : LateralTheory.E.LeafMapFPPf.LeafLimFP` using `LateralTheory.E.LeafLimFPPf.isLimit_pullback_finitelyGenerated`. Establish `a57 : LateralTheory.E.LeafPairRelPf.LeafFactorStage` using `UpperTheory.Cb.descent_map_factors_through_stage`. Establish `a58 : LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap` using `LateralTheory.E.DiagramDescent.LeafDescendPreMap_of a50 a51 a52 a55 a56 a57`. Establish `a59 : LateralTheory.E.LeafSpreadSeparatedPf.LeafClosedImmSpread` using `LateralTheory.E.LeafClosedImmSpreadPf.LeafClosedImmSpread_of`.

Establish `a60 : LateralTheory.E.LeafSpreadSeparatedPf.LeafDiagBC` using `LateralTheory.E.LeafSpreadSeparatedPf.separated_base_change_iff_diagonal_closed_immersion_holds`. Establish `a61 : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated` using `LateralTheory.E.LeafSpreadSeparatedPf.of_two a59 a60`. Establish `a62 : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim` using `LateralTheory.E.LeafSpreadRelDimPf.LeafSpreadRelDim_of`. Establish `a63 : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg` using `LateralTheory.E.StalkOfAlgebra.LeafStalkOfAlg_of`. Establish `a64 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1` using `LateralTheory.E.SpreadingOutSmoothness.LeafSpreadSmooth1_of a62 a63`.

Establish `a65 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend` using `LateralTheory.E.QuasiFiniteAtDescent.LeafQFAtDescend_of`. Establish `a66 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread` using `LateralTheory.E.OpenSpreadingOut.etale_open_spreading_out_over_finitely_generated_subalgebra`. Establish `a67 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap` using `LateralTheory.E.LeafSpreadLQFMap_vtuPfG.LeafSpreadLQFMap_of a65 a66`. Establish `a68 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph` using `LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut.LeafSpreadLQFGraph_of a67`. Establish `a69 : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF` using `LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange.LeafSpreadQF_of a61 a64 a68 a67`.

Establish `a70 : LateralTheory.E.LeafDescendVCut.LeafIrred` using `LateralTheory.E.LeafIrredPf.LeafIrred_of`. Establish `a71 : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth` using `LateralTheory.E.ReducedOfSmooth.LeafReducedSmooth_of`. Establish `a72 : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF` using `LateralTheory.E.QuasiFiniteDescent.goal_of a49 a58 a69 a70 a71 a46`. Establish `a73 : LateralTheory.E.LeafCloseBCut.LeafProjModel` using `LateralTheory.E.LeafProjModelPfImm.LeafProjModel_of`. Establish `a74 : LateralTheory.E.LeafCloseBCut.LeafDimOpen` using `LateralTheory.E.LeafDimOpenPf.LeafDimOpen_of`.

Establish `a75 : LateralTheory.E.LeafSpreadVCut.LeafCloseB` using `LateralTheory.E.LeafCloseBCut.goal_of a73 a74`. Establish `a76 : LateralTheory.E.LeafGeoVV2Cut.LeafExtendZMT` using `UpperTheory.Cb.extension_by_zero_of_zariski_quasi_finite_factorization`. Establish `a77 : LateralTheory.E.LeafGeoVV2Cut.CurveThroughGenericPointSpreadsToSmoothProperFamily` using `LateralTheory.E.LeafGeoVV2Cut.spread_of a72 a75 a76`. Establish `a78 : LateralTheory.E.LeafGeoCut.LeafGeoV` using `LateralTheory.E.LeafGeoVV2Cut.geoV_of a45 a77`. Establish `a79 : LateralTheory.E.LeafGeoCut.LeafClosed` using `LateralTheory.E.LeafClosedPf.LeafClosed_of`.

Establish `a80 : LateralTheory.E.LeafGeoCut.LeafBdry` using `LateralTheory.E.LeafBdryPf.LeafBdry_of`. Establish `a81 : LateralTheory.E.E4.LeafGeo` using `LateralTheory.E.LeafGeoCut.goal_of a78 a79 a80`. Establish `a82 : LateralTheory.E.E4.LeafSpec` using `UpperTheory.Cb.geometric_fibre_cohomology_constant`. Establish `a83 : LateralTheory.E.LeafGhostCut.LeafRelExact` using `LateralTheory.E.LeafGhostCut.relExact`. Establish `a84 : LateralTheory.E.LeafGhostCut.LeafRelNat` using `LateralTheory.E.LeafInj0WPf.leafRelNat`.

Establish `a85 : LateralTheory.E.LeafGhostRelCut.LeafTrunc` using `LateralTheory.E.LeafGhostRelCut.LeafTrunc_of`. Establish `a86 : LateralTheory.KummerTheory.InjSlice` using `LateralTheory.Fin.InjSlice.intersectionNumber_baseChange`. Establish `a87 : LateralTheory.EWeil.AcycPf.RestrInj` using `UpperTheory.Cb.restrInj`. Establish `a88 : LateralTheory.E.LeafConsPf.LeafLoc` using `UpperTheory.leafLocalization_of_injective_slice_of_restriction_injective a86 a87`. Establish `a89 : LateralTheory.E.EtaleTopologySheaves.LeafCons` using `LateralTheory.E.LeafConsPfC.LeafCons_of a88`.

Establish `a90 : LateralTheory.E.LeafDegCut.LeafNeg` using `LateralTheory.E.LeafNegPf.LeafNeg_of`. Establish `a91 : LateralTheory.E.LeafShMapZeroPf.EtaleLift'` using `UpperTheory.Cb.free_etale_sheaf_lift_exists`. Establish `a92 : LateralTheory.E.LeafShMapZeroPf.Gen.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators` using `LateralTheory.E.DegreeZeroGenerators.free_etale_sheaf_zmod_representable_generates`. Establish `a93 : LateralTheory.E.LeafDegCut.LeafShMapZero` using `LateralTheory.E.LeafShMapZeroPf.Glue.LeafShMapZero_of a91 a92`. Establish `a94 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyLocallyLifts` using `LateralTheory.E.H0Lifting.etale_sheaf_epi_lifts_degree_zero_derived_maps_locally`.

Establish `a95 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes` using `LateralTheory.E.H0Kernel.etale_sheaf_zeroth_cohomology_kernel_exact`. Establish `a96 : LateralTheory.E.LeafShIsoPf.Sh.LeafSecRep` using `LateralTheory.E.LeafSecRepPf.LeafSecRep_of`. Establish `a97 : LateralTheory.E.LeafDegCut.LeafShIso` using `LateralTheory.E.LeafShIsoPf.Glue.LeafShIso_of a94 a95 a96`. Establish `a98 : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd` using `UpperTheory.Cb.etale_cohomology_class_killed_on_neighborhood`. Establish `a99 : LateralTheory.E.LeafVan0Pf.LeafVanStalk` using `LateralTheory.E.StalkVanishing.goal_of a98`.

Establish `a100 : LateralTheory.E.LeafVan0Pf.LeafVanW` using `LateralTheory.E.LeafVanWPf.LeafVanW_of`. Establish `a101 : LateralTheory.E.LeafVan0Pf.LeafVanV` using `LateralTheory.E.LeafVanVPf.LeafVanV_of`. Establish `a102 : LateralTheory.E.LeafDegCut.LeafVan0` using `LateralTheory.E.LeafVan0Pf.LeafVan0_of a99 a100 a101`. Establish `a103 : LateralTheory.E.SecondDegreeKilling.LeafPtW` using `LateralTheory.E.PointEvaluationWitness.LeafPtW_of`. Establish `a104 : LateralTheory.E.SecondDegreeKilling.LeafPtV` using `LateralTheory.E.LeafPtVPf.LeafPtV_of`.

Establish `a105 : LateralTheory.E.LeafDegCut.LeafKill2` using `LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKill2_of a98 a103 a104`. Establish `a106 : LateralTheory.E.LeafDegCut.LeafKill1` using `LateralTheory.E.LeafKill1V2Cut.goal_of' a98 a103 a104`. Establish `a107 : LateralTheory.E.LeafSHSysPf.LeafRingSys` using `UpperTheory.Cb.sepClosed_point_filtered_etale_colimit`. Establish `a108 : LateralTheory.E.LeafSHSysPf.LeafNSysGlue` using `LateralTheory.E.NeighbourhoodSystemGluing.LeafNSysGlue_of a107`. Establish `a109 : LateralTheory.E.LeafVanBStalkPf.LeafSHSys` using `LateralTheory.E.LeafSHSysPf.LeafSHSys_of_glue a107 a108`.

Establish `a110 : LateralTheory.E.LeafVanBStalkPf.LeafSHCont` using `UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity`. Establish `a111 : LateralTheory.E.LeafVanBStalkPf.LeafStalkPt` using `LateralTheory.E.LeafVanBStalkPf.stalkPt_of a109 a110`. Establish `a112 : LateralTheory.E.LeafVanBPf.LeafVanBStalk` using `LateralTheory.E.LeafVanBStalkPf.LeafVanBStalk_of_pt a111`. Establish `a113 : LateralTheory.E.LeafVanBPf.LeafClosedSHPos` using `LateralTheory.E.LeafClosedSHPosPf.LeafClosedSHPos_of`. Establish `a114 : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve` using `LateralTheory.E.LeafSHSievePf.LeafSHSieve_of`.

Establish `a115 : LateralTheory.E.LeafVanBPf.LeafClosedSH0` using `LateralTheory.E.LeafClosedSH0PfCut.LeafClosedSH0_of a114`. Establish `a116 : LateralTheory.E.LeafDegCut.LeafVanB` using `LateralTheory.E.LeafVanBPf.LeafVanB_of a112 a113 a115`. Establish `a117 : LateralTheory.E.LeafInj0WPf.LeafSecTw` using `UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing a90`. Establish `a118 : LateralTheory.E.LeafInj0Pf.LeafInj0W` using `LateralTheory.E.LeafInj0WPf.LeafInj0W_of a117`. Establish `a119 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNbSys` using `LateralTheory.E.EtaleNeighbourhoodSystem.LeafSHNbSys_of`.

Establish `a120 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHLoc` using `LateralTheory.E.StrictHenselianLocalization.LeafSHLoc_of`. Establish `a121 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens` using `UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree a90`. Establish `a122 : LateralTheory.E.LeafSHPtPf.LeafSHNb` using `LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNb_of a119 a120 a121`. Establish `a123 : LateralTheory.E.LeafInj0VPf.LeafSHPt` using `LateralTheory.E.StrictHenselianPoint.LeafSHPt_of a122`. Establish `a124 : LateralTheory.E.LeafInj0Pf.LeafInj0V` using `LateralTheory.E.LeafInj0VPf.LeafInj0V_of a123`.

Establish `a125 : LateralTheory.E.LeafDegCut.LeafInj0` using `LateralTheory.E.LeafInj0Pf.LeafInj0_of a118 a124`. Establish `a126 : LateralTheory.E.LeafSurj0Pf.LeafSurj0W` using `LateralTheory.E.LeafSurj0WPf.LeafSurj0W_of`. Establish `a127 : LateralTheory.E.LeafSurj0Pf.LeafSurj0V` using `UpperTheory.Cb.etale_cohomology_degree_zero_surjective_limit`. Establish `a128 : LateralTheory.E.LeafDegCut.LeafSurj0` using `LateralTheory.E.LeafSurj0Pf.LeafSurj0_of a126 a127`. Establish `a129 : LateralTheory.E.EtaleTopologySheaves.LeafDeg` using `LateralTheory.E.LeafDegCut.goal_of a90 a93 a97 a102 a105 a106 a116 a125 a128`.

Establish `a130 : LateralTheory.E.LeafGhostRelCut.LeafRep` using `LateralTheory.E.EtaleTopologySheaves.goal_of a89 a129`. Establish `a131 : LateralTheory.E.LeafGhostCut.LeafGhostRel` using `LateralTheory.E.LeafGhostRelCut.goal_of a85 a130`. Establish `a132 : LateralTheory.E.E4.LeafGhost` using `LateralTheory.E.LeafGhostCut.goal_of_all a83 a84 a131`. Establish `a133 : LateralTheory.E.EtaleChapterEFour` using `LateralTheory.E.E4.goal_of a0 a1 a4 a5 a9 a10 a28 a34 a35 a37 a81 a82 a132`. Conclude with `a133`.
-/
theorem top : LateralTheory.E.EtaleChapterEFour := by
  have a0 : LateralTheory.E.E4.H0TwistOverClosedField := UpperTheory.leafH0_holds
  have a1 : LateralTheory.E.E4.LeafPt := LateralTheory.E.E4.LeafPt_of a0
  have a2 : LateralTheory.E.E4.LeafCoprod := LateralTheory.E.LeafCoprodPf.LeafCoprod_of
  have a3 : LateralTheory.E.E4.LeafCompGeom := LateralTheory.E.E4.leafCompGeom
  have a4 : LateralTheory.E.E4.LeafComp := LateralTheory.E.E4.LeafComp_of a2 a3
  have a5 : LateralTheory.E.E4.LeafDesc := UpperTheory.curve_etale_descent
  have a6 : LateralTheory.E.LeafSSCut.LeafFilt := LateralTheory.E.LeafFiltPf.LeafFilt_of
  have a7 : LateralTheory.E.LeafSSCut.LeafCompare := LateralTheory.E.DiagonalComparison.LeafCompare_of
  have a8 : LateralTheory.E.LeafSSCut.LeafTerms := LateralTheory.E.LeafTermsPf.LeafTerms_of
  have a9 : LateralTheory.E.E4.LeafSS := LateralTheory.E.LeafSSCut.goal_of a6 a7 a8
  have a10 : LateralTheory.E.E4.LeafUnits := LateralTheory.E.CurveUnitsOrderAtInfinity.LeafUnits_of
  have a11 : LateralTheory.E.LeafPicCut.LeafSelPic := LateralTheory.E.LeafSelPicPf.LeafSelPic_of
  have a12 : LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := UpperTheory.integralClosure_finite_of_finiteType_domain
  have a13 : LateralTheory.E.LeafNormalModelPf.LeafIntClosureAlg := LateralTheory.E.LeafIntClosureAlgPf.LeafIntClosureAlg_of a12
  have a14 : LateralTheory.E.LeafGlueProperPf.LeafGlueExists := LateralTheory.E.GluingExistence.LeafGlueExists_of
  have a15 : LateralTheory.E.LeafGlueProperPf.LeafGlueIntegral := LateralTheory.E.LeafGlueProperPf.glued_affine_curve_is_integral_scheme
  have a16 : LateralTheory.E.LeafGlueProperPf.LeafGlueNormal := LateralTheory.E.LeafGlueProperPf.glued_affine_curve_stalks_integrally_closed
  have a17 : LateralTheory.E.LeafGlueProperPf.LeafGlueDim := LateralTheory.E.LeafGlueDimPf.LeafGlueDim_of
  have a18 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueSep := LateralTheory.E.GluedCurveSeparated.LeafGlueSep_of
  have a19 : LateralTheory.E.LeafGlueIsProperPf.LeafGlueExistence := UpperTheory.Cb.properGluing_existence
  have a20 : LateralTheory.E.LeafGlueProperPf.LeafGlueIsProper := LateralTheory.E.LeafGlueIsProperPf.LeafGlueIsProper_of a18 a19
  have a21 : LateralTheory.E.LeafGlueProperPf.LeafGlueGeneric := LateralTheory.E.LeafGlueGenericPf.glued_curve_generic_point_maps_to_function_field
  have a22 : LateralTheory.E.LeafNormalModelPf.LeafGlueProper := LateralTheory.E.LeafGlueProperPf.LeafGlueProper_of a14 a15 a16 a17 a20 a21
  have a23 : LateralTheory.E.LeafModelCurveCut.ExistsNormalProperCurveModel := LateralTheory.E.LeafNormalModelPf.LeafNormalModel_of a13 a22
  have a24 : LateralTheory.E.LeafSmoothOfNormalPf.LeafStalkSmoothClosed := LateralTheory.E.LeafStalkSmoothClosedPf.LeafStalkSmoothClosed_of
  have a25 : LateralTheory.E.LeafSmoothOfNormalPf.LeafRelDimOne := LateralTheory.E.LeafRelDimOnePf.LeafRelDimOne_of
  have a26 : LateralTheory.E.LeafModelCurveCut.LeafSmoothOfNormal := LateralTheory.E.LeafSmoothOfNormalPf.LeafSmoothOfNormal_of a24 a25
  have a27 : LateralTheory.E.LeafCurveVCut.LeafModelCurve := LateralTheory.E.LeafModelCurveCut.goal_of a23 a26
  have a28 : LateralTheory.E.E4.LeafPic := UpperTheory.curve_picard_of_selmerPicard_of_modelCurve a11 a27
  have a29 : LateralTheory.E.LeafTwistPf.LeafLoc := LateralTheory.E.LeafTwistIsoPf.leafLoc
  have a30 : LateralTheory.E.LeafTwistPf.LeafTwSec := LateralTheory.E.LeafTwistIsoPf.leafTwSec
  have a31 : LateralTheory.E.LeafKumCut.LeafTwist := LateralTheory.E.LeafTwistPf.LeafTwist_of a29 a30
  have a32 : LateralTheory.E.LeafKumCut.EtaleFirstCohomologyMultiplicativeGroupPicard := (fun _ => hB6)
  have a33 : LateralTheory.E.LeafKumCut.LeafKumSeq := LateralTheory.E.LeafKumFieldPf.kumSeq
  have a34 : LateralTheory.E.E4.LeafKum := LateralTheory.E.LeafKumCut.goal_of a31 a32 a33
  have a35 : LateralTheory.E.E4.LeafCurve := UpperTheory.leafCurve_of_leafH0 a0
  have a36 : LateralTheory.E.LeafKillCut.LeafOne := UpperTheory.Cb.curve_cohomology_killed_by_finite_cover a0
  have a37 : LateralTheory.E.E4.LeafKill := LateralTheory.E.LeafKillCut.goal_of a36
  have a38 : LateralTheory.E.LeafCurveVCut.LeafFibreField := LateralTheory.E.LeafFibreFieldPf.LeafFibreField_of
  have a39 : LateralTheory.E.LeafCurveVCut.LeafTrdegDim := LateralTheory.E.LeafTrdegDimPf.LeafTrdegDim_of
  have a40 : LateralTheory.E.LeafCurveVCut.LeafBaseChangeField := LateralTheory.E.LeafBaseChangeFieldPf.LeafBaseChangeField_of
  have a41 : LateralTheory.E.LeafExtendCut.LeafStalkValuation := LateralTheory.E.LeafStalkValuationPf.LeafStalkValuation_of
  have a42 : LateralTheory.E.LeafExtendCut.LeafLocalExtend := LateralTheory.E.LeafLocalExtendPf.LeafLocalExtend_of
  have a43 : LateralTheory.E.LeafExtendCut.LeafGlueExtend := LateralTheory.E.LeafGlueExtendPf.LeafGlueExtend_of
  have a44 : LateralTheory.E.LeafCurveVCut.LeafExtend := LateralTheory.E.LeafExtendCut.goal_of a41 a42 a43
  have a45 : LateralTheory.E.LeafGeoVCut.LeafCurveV := LateralTheory.E.LeafCurveVCut.goal_of a38 a39 a40 a27 a44
  have a46 : LateralTheory.E.LeafDescendVCut.LeafDimBound := LateralTheory.E.LeafDimBoundPf.LeafDimBound_of
  have a47 : LateralTheory.E.QuotientFieldNonconstantLift.LeafCurveSmall := LateralTheory.E.CurveKrullDim.LeafCurveSmall_of a46
  have a48 : LateralTheory.E.QuotientFieldNonconstantLift.LeafLiftNonconst := LateralTheory.E.NonconstantLift.LeafLiftNonconst_of
  have a49 : LateralTheory.E.QuasiFiniteDescent.LeafQFOmega := LateralTheory.E.QuotientFieldNonconstantLift.LeafQFOmega_of a47 a48
  have a50 : LateralTheory.E.LeafObjFPPf.LeafObjAff := LateralTheory.E.LeafObjAffPf.LeafObjAff_of
  have a51 : LateralTheory.E.LeafObjGluePf.LeafGlueTwo := LateralTheory.E.LeafGlueTwoPfQS.LeafGlueTwo_of
  have a52 : LateralTheory.E.LeafObjFPPf.LeafQCQSInduct := LateralTheory.E.LeafQCQSInductPf.LeafQCQSInduct_of
  have a53 : LateralTheory.E.LeafInclPiecePf.LeafInclMap := UpperTheory.Cb.pullback_isLimit_over_fg_subalgebras
  have a54 : LateralTheory.E.LeafInclPiecePf.LeafInclOpen := UpperTheory.Cb.isOpenImmersion_inclusion_of_piecewise
  have a55 : LateralTheory.E.LeafInclDescendPf.LeafInclPiece := LateralTheory.E.LeafInclPiecePf.LeafInclPiece_of a53 a54
  have a56 : LateralTheory.E.LeafMapFPPf.LeafLimFP := LateralTheory.E.LeafLimFPPf.isLimit_pullback_finitelyGenerated
  have a57 : LateralTheory.E.LeafPairRelPf.LeafFactorStage := UpperTheory.Cb.descent_map_factors_through_stage
  have a58 : LateralTheory.E.QuasiFiniteDescent.LeafDescendPreMap := LateralTheory.E.DiagramDescent.LeafDescendPreMap_of a50 a51 a52 a55 a56 a57
  have a59 : LateralTheory.E.LeafSpreadSeparatedPf.LeafClosedImmSpread := LateralTheory.E.LeafClosedImmSpreadPf.LeafClosedImmSpread_of
  have a60 : LateralTheory.E.LeafSpreadSeparatedPf.LeafDiagBC := LateralTheory.E.LeafSpreadSeparatedPf.separated_base_change_iff_diagonal_closed_immersion_holds
  have a61 : LateralTheory.E.LeafSpreadProperPf.LeafSpreadSeparated := LateralTheory.E.LeafSpreadSeparatedPf.of_two a59 a60
  have a62 : LateralTheory.E.LeafSpreadSmoothPf.LeafSpreadRelDim := LateralTheory.E.LeafSpreadRelDimPf.LeafSpreadRelDim_of
  have a63 : LateralTheory.E.SpreadingOutSmoothness.LeafStalkOfAlg := LateralTheory.E.StalkOfAlgebra.LeafStalkOfAlg_of
  have a64 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadSmooth1 := LateralTheory.E.SpreadingOutSmoothness.LeafSpreadSmooth1_of a62 a63
  have a65 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := LateralTheory.E.QuasiFiniteAtDescent.LeafQFAtDescend_of
  have a66 : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafOpenSpread := LateralTheory.E.OpenSpreadingOut.etale_open_spreading_out_over_finitely_generated_subalgebra
  have a67 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFMap := LateralTheory.E.LeafSpreadLQFMap_vtuPfG.LeafSpreadLQFMap_of a65 a66
  have a68 : LateralTheory.E.SpreadingOutQuasiFiniteness.LeafSpreadLQFGraph := LateralTheory.E.LocallyQuasiFiniteGraphSpreadingOut.LeafSpreadLQFGraph_of a67
  have a69 : LateralTheory.E.QuasiFiniteDescent.LeafSpreadQF := LateralTheory.E.SpreadingOutQuasiFinitenessBaseChange.LeafSpreadQF_of a61 a64 a68 a67
  have a70 : LateralTheory.E.LeafDescendVCut.LeafIrred := LateralTheory.E.LeafIrredPf.LeafIrred_of
  have a71 : LateralTheory.E.QuasiFiniteDescent.LeafReducedSmooth := LateralTheory.E.ReducedOfSmooth.LeafReducedSmooth_of
  have a72 : LateralTheory.E.LeafGeoVV2Cut.LeafDescendQF := LateralTheory.E.QuasiFiniteDescent.goal_of a49 a58 a69 a70 a71 a46
  have a73 : LateralTheory.E.LeafCloseBCut.LeafProjModel := LateralTheory.E.LeafProjModelPfImm.LeafProjModel_of
  have a74 : LateralTheory.E.LeafCloseBCut.LeafDimOpen := LateralTheory.E.LeafDimOpenPf.LeafDimOpen_of
  have a75 : LateralTheory.E.LeafSpreadVCut.LeafCloseB := LateralTheory.E.LeafCloseBCut.goal_of a73 a74
  have a76 : LateralTheory.E.LeafGeoVV2Cut.LeafExtendZMT := UpperTheory.Cb.extension_by_zero_of_zariski_quasi_finite_factorization
  have a77 : LateralTheory.E.LeafGeoVV2Cut.CurveThroughGenericPointSpreadsToSmoothProperFamily := LateralTheory.E.LeafGeoVV2Cut.spread_of a72 a75 a76
  have a78 : LateralTheory.E.LeafGeoCut.LeafGeoV := LateralTheory.E.LeafGeoVV2Cut.geoV_of a45 a77
  have a79 : LateralTheory.E.LeafGeoCut.LeafClosed := LateralTheory.E.LeafClosedPf.LeafClosed_of
  have a80 : LateralTheory.E.LeafGeoCut.LeafBdry := LateralTheory.E.LeafBdryPf.LeafBdry_of
  have a81 : LateralTheory.E.E4.LeafGeo := LateralTheory.E.LeafGeoCut.goal_of a78 a79 a80
  have a82 : LateralTheory.E.E4.LeafSpec := UpperTheory.Cb.geometric_fibre_cohomology_constant
  have a83 : LateralTheory.E.LeafGhostCut.LeafRelExact := LateralTheory.E.LeafGhostCut.relExact
  have a84 : LateralTheory.E.LeafGhostCut.LeafRelNat := LateralTheory.E.LeafInj0WPf.leafRelNat
  have a85 : LateralTheory.E.LeafGhostRelCut.LeafTrunc := LateralTheory.E.LeafGhostRelCut.LeafTrunc_of
  have a86 : LateralTheory.KummerTheory.InjSlice := LateralTheory.Fin.InjSlice.intersectionNumber_baseChange
  have a87 : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restrInj
  have a88 : LateralTheory.E.LeafConsPf.LeafLoc := UpperTheory.leafLocalization_of_injective_slice_of_restriction_injective a86 a87
  have a89 : LateralTheory.E.EtaleTopologySheaves.LeafCons := LateralTheory.E.LeafConsPfC.LeafCons_of a88
  have a90 : LateralTheory.E.LeafDegCut.LeafNeg := LateralTheory.E.LeafNegPf.LeafNeg_of
  have a91 : LateralTheory.E.LeafShMapZeroPf.EtaleLift' := UpperTheory.Cb.free_etale_sheaf_lift_exists
  have a92 : LateralTheory.E.LeafShMapZeroPf.Gen.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := LateralTheory.E.DegreeZeroGenerators.free_etale_sheaf_zmod_representable_generates
  have a93 : LateralTheory.E.LeafDegCut.LeafShMapZero := LateralTheory.E.LeafShMapZeroPf.Glue.LeafShMapZero_of a91 a92
  have a94 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyLocallyLifts := LateralTheory.E.H0Lifting.etale_sheaf_epi_lifts_degree_zero_derived_maps_locally
  have a95 : LateralTheory.E.LeafShIsoPf.EtaleDerivedDegreeZeroHomologyKernelLocallyVanishes := LateralTheory.E.H0Kernel.etale_sheaf_zeroth_cohomology_kernel_exact
  have a96 : LateralTheory.E.LeafShIsoPf.Sh.LeafSecRep := LateralTheory.E.LeafSecRepPf.LeafSecRep_of
  have a97 : LateralTheory.E.LeafDegCut.LeafShIso := LateralTheory.E.LeafShIsoPf.Glue.LeafShIso_of a94 a95 a96
  have a98 : LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKillNbhd := UpperTheory.Cb.etale_cohomology_class_killed_on_neighborhood
  have a99 : LateralTheory.E.LeafVan0Pf.LeafVanStalk := LateralTheory.E.StalkVanishing.goal_of a98
  have a100 : LateralTheory.E.LeafVan0Pf.LeafVanW := LateralTheory.E.LeafVanWPf.LeafVanW_of
  have a101 : LateralTheory.E.LeafVan0Pf.LeafVanV := LateralTheory.E.LeafVanVPf.LeafVanV_of
  have a102 : LateralTheory.E.LeafDegCut.LeafVan0 := LateralTheory.E.LeafVan0Pf.LeafVan0_of a99 a100 a101
  have a103 : LateralTheory.E.SecondDegreeKilling.LeafPtW := LateralTheory.E.PointEvaluationWitness.LeafPtW_of
  have a104 : LateralTheory.E.SecondDegreeKilling.LeafPtV := LateralTheory.E.LeafPtVPf.LeafPtV_of
  have a105 : LateralTheory.E.LeafDegCut.LeafKill2 := LateralTheory.E.SecondDegreeKilling.Nbhd.LeafKill2_of a98 a103 a104
  have a106 : LateralTheory.E.LeafDegCut.LeafKill1 := LateralTheory.E.LeafKill1V2Cut.goal_of' a98 a103 a104
  have a107 : LateralTheory.E.LeafSHSysPf.LeafRingSys := UpperTheory.Cb.sepClosed_point_filtered_etale_colimit
  have a108 : LateralTheory.E.LeafSHSysPf.LeafNSysGlue := LateralTheory.E.NeighbourhoodSystemGluing.LeafNSysGlue_of a107
  have a109 : LateralTheory.E.LeafVanBStalkPf.LeafSHSys := LateralTheory.E.LeafSHSysPf.LeafSHSys_of_glue a107 a108
  have a110 : LateralTheory.E.LeafVanBStalkPf.LeafSHCont := UpperTheory.Cb.etale_stalk_cohomology_strictHenselian_continuity
  have a111 : LateralTheory.E.LeafVanBStalkPf.LeafStalkPt := LateralTheory.E.LeafVanBStalkPf.stalkPt_of a109 a110
  have a112 : LateralTheory.E.LeafVanBPf.LeafVanBStalk := LateralTheory.E.LeafVanBStalkPf.LeafVanBStalk_of_pt a111
  have a113 : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := LateralTheory.E.LeafClosedSHPosPf.LeafClosedSHPos_of
  have a114 : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := LateralTheory.E.LeafSHSievePf.LeafSHSieve_of
  have a115 : LateralTheory.E.LeafVanBPf.LeafClosedSH0 := LateralTheory.E.LeafClosedSH0PfCut.LeafClosedSH0_of a114
  have a116 : LateralTheory.E.LeafDegCut.LeafVanB := LateralTheory.E.LeafVanBPf.LeafVanB_of a112 a113 a115
  have a117 : LateralTheory.E.LeafInj0WPf.LeafSecTw := UpperTheory.Cb.twistedSections_of_negativeDegreeVanishing a90
  have a118 : LateralTheory.E.LeafInj0Pf.LeafInj0W := LateralTheory.E.LeafInj0WPf.LeafInj0W_of a117
  have a119 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNbSys := LateralTheory.E.EtaleNeighbourhoodSystem.LeafSHNbSys_of
  have a120 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHLoc := LateralTheory.E.StrictHenselianLocalization.LeafSHLoc_of
  have a121 : LateralTheory.E.StrictHenselianNeighbourhood.LeafSHHens := UpperTheory.Cb.strictlyHenselianLocal_of_negligibleDegree a90
  have a122 : LateralTheory.E.LeafSHPtPf.LeafSHNb := LateralTheory.E.StrictHenselianNeighbourhood.LeafSHNb_of a119 a120 a121
  have a123 : LateralTheory.E.LeafInj0VPf.LeafSHPt := LateralTheory.E.StrictHenselianPoint.LeafSHPt_of a122
  have a124 : LateralTheory.E.LeafInj0Pf.LeafInj0V := LateralTheory.E.LeafInj0VPf.LeafInj0V_of a123
  have a125 : LateralTheory.E.LeafDegCut.LeafInj0 := LateralTheory.E.LeafInj0Pf.LeafInj0_of a118 a124
  have a126 : LateralTheory.E.LeafSurj0Pf.LeafSurj0W := LateralTheory.E.LeafSurj0WPf.LeafSurj0W_of
  have a127 : LateralTheory.E.LeafSurj0Pf.LeafSurj0V := UpperTheory.Cb.etale_cohomology_degree_zero_surjective_limit
  have a128 : LateralTheory.E.LeafDegCut.LeafSurj0 := LateralTheory.E.LeafSurj0Pf.LeafSurj0_of a126 a127
  have a129 : LateralTheory.E.EtaleTopologySheaves.LeafDeg := LateralTheory.E.LeafDegCut.goal_of a90 a93 a97 a102 a105 a106 a116 a125 a128
  have a130 : LateralTheory.E.LeafGhostRelCut.LeafRep := LateralTheory.E.EtaleTopologySheaves.goal_of a89 a129
  have a131 : LateralTheory.E.LeafGhostCut.LeafGhostRel := LateralTheory.E.LeafGhostRelCut.goal_of a85 a130
  have a132 : LateralTheory.E.E4.LeafGhost := LateralTheory.E.LeafGhostCut.goal_of_all a83 a84 a131
  have a133 : LateralTheory.E.EtaleChapterEFour := LateralTheory.E.E4.goal_of a0 a1 a4 a5 a9 a10 a28 a34 a35 a37 a81 a82 a132
  exact a133

end UpperTheory.Et.EtaleTopology
