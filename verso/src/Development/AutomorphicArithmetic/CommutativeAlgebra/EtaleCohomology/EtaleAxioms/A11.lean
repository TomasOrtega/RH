import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdLeafLocOfLeafLevel
import Development.AutomorphicArithmetic.CommutativeAlgebra.LeafProdHolds
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineLeafOfProjectiveLeaves
import Development.EtaleCohomology.EtaleSheaves.ChartAwayPf
import Development.EtaleCohomology.EtaleSheaves.ChartGeoPf
import Development.EtaleCohomology.EtaleSheaves.AwSpec
import Development.EtaleCohomology.EtaleSheaves.LeafChartAffPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartAwayPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartPf
import Development.EtaleCohomology.EtaleSheaves.LeafChartRingPf
import Development.EtaleCohomology.EtaleSheaves.LeafCokIsoPf
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPfNakH
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointPf
import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfY
import Development.EtaleCohomology.EtaleSheaves.LeafCov1Of
import Development.EtaleCohomology.EtaleSheaves.EtLocOfOpens
import Development.EtaleCohomology.EtaleSheaves.LeafDiscPf
import Development.EtaleCohomology.EtaleSheaves.ConeExcision.ExcisionOfCokernel
import Development.EtaleCohomology.EtaleSheaves.LeafExcRingOf
import Development.EtaleCohomology.EtaleSheaves.LeafFreeLocPf
import Development.EtaleCohomology.EtaleSheaves.LeafHIPf
import Development.EtaleCohomology.EtaleSheaves.LeafJacobianPf
import Development.EtaleCohomology.EtaleSheaves.LeafLevelPf
import Development.EtaleCohomology.EtaleSheaves.LeafPolyEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafProjPf
import Development.EtaleCohomology.EtaleSheaves.LeafQuotEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafRelPf
import Development.EtaleCohomology.EtaleSheaves.LeafResDimQePf
import Development.EtaleCohomology.EtaleSheaves.LeafResKerPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofEtPf
import Development.EtaleCohomology.EtaleSheaves.LeafRoofPf
import Development.EtaleCohomology.EtaleSheaves.LeafSqPf
import Development.EtaleCohomology.EtaleSheaves.SheafPushoutSquare
import Development.EtaleCohomology.EtaleSheaves.ChainTower
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

namespace UpperTheory.Et.E6

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a0 : LateralTheory.E.t_E6Cut.LeafRel := LateralTheory.E.t_E6Cut.LeafRel_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a1 : LateralTheory.E.LeafLevelPf.LeafDisc := LateralTheory.E.LeafDiscPf.LeafDisc_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a2 : LateralTheory.E.LeafLevelPf.LeafFilt := LateralTheory.E.ChainTower.LeafFilt_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a3 : LateralTheory.E.t_E6Cut.LeafLevel := LateralTheory.E.LeafLevelPf.LeafLevel_of a0 a1 a2
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a4 : LateralTheory.E.t_E6Cut.LeafProd := UpperTheory.leafProd_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a5 : LateralTheory.E.t_E6Cut.LeafLoc := UpperTheory.leafProd_leafLoc_of_leafLevel a3 a4
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a6 : LateralTheory.E.LeafSqPf.LeafSheafPush := LateralTheory.E.SheafPushoutSquare.LeafSheafPush_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a7 : LateralTheory.E.LeafSqPf.LeafFreeLoc := LateralTheory.E.LeafFreeLocPf.LeafFreeLoc_of a0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a8 : LateralTheory.E.LeafExcPf.LeafSq := LateralTheory.E.LeafSqPf.square_of_pushout_and_free_local a6 a7
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a9 : LateralTheory.E.LeafExcPf.LeafCokIso := LateralTheory.E.LeafCokIsoPf.LeafCokIso_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a10 : LateralTheory.E.t_E6Cut.LeafExc := LateralTheory.E.LeafExcPf.excision_of_cokernel a0 a8 a9
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a11 : LateralTheory.E.LeafExcRingPf.LeafCov1 := LateralTheory.E.LeafCov1Pf.LeafCov1_of a10
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a12 : LateralTheory.E.LeafExcRingPf.LeafCov2 := LateralTheory.E.LeafCov2Pf.LeafCov2_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a13 : LateralTheory.E.t_E6Cut.LeafExcRing := LateralTheory.E.LeafExcRingPf2.LeafExcRing_of' a10 a11 a12
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a14 : LateralTheory.E.LeafRoofEtPPf.LeafQuotEt := LateralTheory.E.LeafQuotEtPf.LeafQuotEt_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a15 : LateralTheory.E.LeafRoofEtPPf.LeafPolyEt := LateralTheory.E.LeafPolyEtPf.LeafPolyEt_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a16 : LateralTheory.E.LeafRoofEtPf.LeafRoofEtP := LateralTheory.E.LeafRoofEtPPf.roofEtale_of_quotientEtale_polynomialEtale a14 a15
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a17 : LateralTheory.E.LeafRoofPf.LeafRoofEt := LateralTheory.E.LeafRoofEtPf.LeafRoofEt_of a16
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a18 : LateralTheory.E.t_E6Cut.LeafRoof := LateralTheory.E.LeafRoofPf.LeafRoof_of a17
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a19 : LateralTheory.E.LeafCoordsPointResPf.LeafResDimQe := LateralTheory.E.LeafResDimQePf.LeafResDimQe_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a20 : LateralTheory.E.LeafCoordsPointResPf.LeafResKer := LateralTheory.E.LeafCoordsPointResPf.LeafResKer_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a21 : LateralTheory.E.LeafCoordsPointPf.LeafCoordsPointRes := LateralTheory.E.LeafCoordsPointResPf.LeafCoordsPointRes_of_leaves a19 a20
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a22 : LateralTheory.E.LeafCoordsPf.LeafCoordsPoint := LateralTheory.E.LeafCoordsPointPf.LeafCoordsPoint_of_res a21
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a23 : LateralTheory.E.LeafChartRingPf.LeafCoords := LateralTheory.E.LeafCoordsPf.NakH.LeafCoords_of_point a22
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a24 : LateralTheory.E.LeafChartRingPf.LeafJacobian := LateralTheory.E.LeafJacobianPf.LeafJacobian_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a25 : LateralTheory.E.t_E6Cut.LeafChartRing := LateralTheory.E.LeafChartRingPf.LeafChartRing_of a23 a24
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a26 : LateralTheory.E.ChartGeoPf.ChartStdGeo := LateralTheory.E.ChartGeoPf.chartStdGeo_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a27 : LateralTheory.E.ChartGeoPf.RangeKer := LateralTheory.E.ChartGeoPf.rangeKer_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a28 : LateralTheory.E.ChartGeoPf.QuotLoc := LateralTheory.E.ChartGeoPf.quotLoc_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a29 : LateralTheory.E.LeafChartAffPf.ChartGeo := LateralTheory.E.ChartGeoPf.ChartGeo_of_parts a26 a27 a28
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a30 : LateralTheory.E.LeafChartAffPf.ChartAway := LateralTheory.E.ChartAwayPf.ChartAway_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a31 : LateralTheory.E.LeafChartPf.LeafChartAff := LateralTheory.E.LeafChartAffPf.LeafChartAff_of a29 a30
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a32 : LateralTheory.E.LeafChartPf.LeafChartAway := LateralTheory.E.LeafChartAwayPf.LeafChartAway_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a33 : LateralTheory.E.t_E6Cut.LeafChart := LateralTheory.E.LeafChartPf.LeafChart_of a25 a31 a32
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a34 : LateralTheory.E.D2.LeafA6nat := LateralTheory.Fix.EtaleChapterDTwo.s0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a35 : LateralTheory.E.t_E6Cut.LeafNat := (fun (h : LateralTheory.E.D2.LeafA6nat) _ _ _ _ _ => h) a34
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a36 : LateralTheory.E.t_E6Cut.LeafProj := LateralTheory.E.LeafProjPf.LeafProj_of a35
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a37 : LateralTheory.E.t_E6Cut.LeafHI := LateralTheory.E.LeafHIPf.LeafHI_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a38 : LateralTheory.E.t_E6Cut.LeafAff := UpperTheory.Cb.affine_leaf_of_projective_leaves a36 a10 a37
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem a39 : LateralTheory.E.EtaleChapterESix := LateralTheory.E.t_E6Cut.goal_of a5 a13 a18 a33 a38

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterESix := a39

end UpperTheory.Et.E6
