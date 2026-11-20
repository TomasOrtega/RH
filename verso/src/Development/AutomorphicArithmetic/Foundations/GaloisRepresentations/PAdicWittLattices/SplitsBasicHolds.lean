import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultiSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesAbs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PCoverInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPieceLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct

universe u v

namespace UpperTheory.Gal.G3

/- English proof (translation)
The claim follows from `@pIsoPts`.
-/
theorem isoPts_holds : IsoPts := @pIsoPts

/- English proof (translation)
The claim follows from `@pPtsOfSplits`.
-/
theorem ptsOfSplits_holds : PtsOfSplits := @pPtsOfSplits

/- English proof (translation)
The claim follows from `pSplitsPts isoPts_holds`.
-/
theorem splitsPts_holds : SplitsPts := pSplitsPts isoPts_holds

/- English proof (translation)
The claim follows from `@pExtPts`.
-/
theorem extPts_holds : ExtPts := @pExtPts

/- English proof (translation)
The claim follows from `pFEtBasic ptsOfSplits_holds`.
-/
theorem fEtBasic_holds : FEtBasic := pFEtBasic ptsOfSplits_holds

/- English proof (translation)
The claim follows from `pSplitsBasic splitsPts_holds ptsOfSplits_holds`.
-/
theorem splitsBasic_holds : SplitsBasic := pSplitsBasic splitsPts_holds ptsOfSplits_holds

/- English proof (translation)
The claim follows from `pSplitsComp splitsPts_holds ptsOfSplits_holds`.
-/
theorem splitsComp_holds : SplitsComp := pSplitsComp splitsPts_holds ptsOfSplits_holds

/- English proof (translation)
The claim follows from `@pBcSplits @splitsBasic_holds`.
-/
theorem bcSplits_holds : BcSplits := @pBcSplits @splitsBasic_holds

/- English proof (translation)
The claim follows from `pBcGal bcSplits_holds`.
-/
theorem bcGal_holds : BcGal := pBcGal bcSplits_holds

/- English proof (translation)
The claim follows from `@pOrdStep`.
-/
theorem ordStep_holds : OrdStep := @pOrdStep

/- English proof (translation)
The claim follows from `pOrdEx ordStep_holds`.
-/
theorem ordEx_holds : OrdEx := pOrdEx ordStep_holds

/- English proof (translation)
The claim follows from `pGalClosD splitsPts_holds ordEx_holds`.
-/
theorem galClosD_holds : GalClosD := pGalClosD splitsPts_holds ordEx_holds

/- English proof (translation)
The claim follows from `pGalClos galClosD_holds`.
-/
theorem galClos_holds : GalClos := pGalClos galClosD_holds

/- English proof (translation)
The claim follows from `pMultiSplit fEtBasic_holds splitsBasic_holds galClosD_holds`.
-/
theorem multiSplit_holds : MultiSplit := pMultiSplit fEtBasic_holds splitsBasic_holds galClosD_holds

/- English proof (translation)
The claim follows from `pAlgIsoPts isoPts_holds`.
-/
theorem algIsoPts_holds : AlgIsoPts := pAlgIsoPts isoPts_holds

/- English proof (translation)
The claim follows from `@pAlgSplit @algIsoPts_holds`.
-/
theorem algSplit_holds : AlgSplit := @pAlgSplit @algIsoPts_holds

/- English proof (translation)
The claim follows from `@pAlgTr`.
-/
theorem algTr_holds : AlgTr := @pAlgTr

/- English proof (translation)
The claim follows from `pHodgeFun ptsOfSplits_holds algSplit_holds algTr_holds`.
-/
theorem hodgeFun_holds : ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := pHodgeFun ptsOfSplits_holds algSplit_holds algTr_holds

/- English proof (translation)
The claim follows from `@pHodgeTr @hodgeFun_holds`.
-/
theorem hodgeTr_holds : HodgeTr := @pHodgeTr @hodgeFun_holds

/- English proof (translation)
The claim follows from `@pHodgeInj`.
-/
theorem hodgeInj_holds : HodgeInj := @pHodgeInj

/- English proof (translation)
The claim follows from `@pHodgeGood @hodgeTr_holds @hodgeInj_holds`.
-/
theorem hodgeGood_holds : HodgeGood := @pHodgeGood @hodgeTr_holds @hodgeInj_holds

/- English proof (translation)
The claim follows from `@pEtTr`.
-/
theorem etTr_holds : EtTr := @pEtTr

/- English proof (translation)
The claim follows from `@pEtnGood @fEtBasic_holds @etTr_holds`.
-/
theorem etnGood_holds : EtnGood := @pEtnGood @fEtBasic_holds @etTr_holds

/- English proof (translation)
The claim follows from `@pEtGood @etnGood_holds`.
-/
theorem etGood_holds : EtGood := @pEtGood @etnGood_holds

/- English proof (translation)
The claim follows from `pBcGood bcSplits_holds bcGal_holds`.
-/
theorem bcGood_holds : BcGood.{u} := pBcGood bcSplits_holds bcGal_holds

/- English proof (translation)
The claim follows from `@pExtTr.{u}`.
-/
theorem extTr_holds : ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) :=
  @pExtTr.{u}

/- English proof (translation)
The claim follows from `pExtGood extTr_holds`.
-/
theorem extGood_holds : ExtGood.{u} := pExtGood extTr_holds

/- English proof (translation)
The claim follows from `@pOpTr.{u}`.
-/
theorem opTr_holds : OpTr.{u} := @pOpTr.{u}

/- English proof (translation)
The claim follows from `pOpEx opTr_holds`.
-/
theorem opEx_holds : OpEx.{u} := pOpEx opTr_holds

/- English proof (translation)
The claim follows from `@pGalInv.{u}`.
-/
theorem galInv_holds : GalInv.{u} := @pGalInv.{u}

/- English proof (translation)
The claim follows from `@pOpEt`.
-/
theorem opEt_holds : OpEt := @pOpEt

/- English proof (translation)
The claim follows from `pOpBc bcSplits_holds bcGal_holds`.
-/
theorem opBc_holds : OpBc.{u} := pOpBc bcSplits_holds bcGal_holds

/- English proof (translation)
The claim follows from `pFEtInj galClosD_holds`.
-/
theorem fEtInj_holds : FEtInj.{u} := pFEtInj galClosD_holds

/- English proof (translation)
The claim follows from `pTrBase fEtBasic_holds splitsBasic_holds galClosD_holds`.
-/
theorem trBase_holds : TrBase.{u} := pTrBase fEtBasic_holds splitsBasic_holds galClosD_holds

/- English proof (translation)
The claim follows from `pTrPushM fEtBasic_holds splitsBasic_holds splitsComp_holds multiSplit_holds fEtInj_holds`.
-/
theorem trPushM_holds : TrPushM.{u} := pTrPushM fEtBasic_holds splitsBasic_holds splitsComp_holds multiSplit_holds fEtInj_holds

/- English proof (translation)
The claim follows from `pLiesAbs fEtBasic_holds trBase_holds trPushM_holds`.
-/
theorem liesAbs_holds : LiesAbs.{u} := pLiesAbs fEtBasic_holds trBase_holds trPushM_holds

/- English proof (translation)
The claim follows from `pHopSpec etGood_holds bcGood_holds galClos_holds opEx_holds opTr_holds opEt_holds opBc_holds bcSplits_holds`.
-/
theorem hopSpec_holds : HopSpec := pHopSpec etGood_holds bcGood_holds galClos_holds opEx_holds opTr_holds opEt_holds opBc_holds bcSplits_holds

/- English proof (translation)
The claim follows from `@pLiesGen`.
-/
theorem liesGen_holds : LiesGen := @pLiesGen

/- English proof (translation)
The claim follows from `pLiesOp liesGen_holds liesAbs_holds`.
-/
theorem liesOp_holds : LiesOp.{u} := pLiesOp liesGen_holds liesAbs_holds

/- English proof (translation)
The claim follows from `pCoverInv galInv_holds splitsPts_holds`.
-/
theorem coverInv_holds : CoverInv.{u} := pCoverInv galInv_holds splitsPts_holds

/- English proof (translation)
The claim follows from `pPieceLe etGood_holds bcGood_holds extGood_holds extTr_holds hopSpec_holds coverInv_holds`.
-/
theorem pieceLe_holds : PieceLe := pPieceLe etGood_holds bcGood_holds extGood_holds extTr_holds hopSpec_holds coverInv_holds

/- English proof (translation)
The claim follows from `pTwSplit splitsPts_holds`.
-/
theorem twSplit_holds : TwSplit := pTwSplit splitsPts_holds

/- English proof (translation)
The claim follows from `pTwGal twSplit_holds`.
-/
theorem twGal_holds : TwGal := pTwGal twSplit_holds

/- English proof (translation)
The claim follows from `@pPlInv.{u} @galInv_holds.{u} @twGal_holds`.
-/
theorem plInv_holds : PlInv.{u} := @pPlInv.{u} @galInv_holds.{u} @twGal_holds

/- English proof (translation)
The claim follows from `@pHopDeep.{u} @plInv_holds.{u}`.
-/
theorem hopDeep_holds : HopDeep.{u} := @pHopDeep.{u} @plInv_holds.{u}

/- English proof (translation)
The claim follows from `@pHopEx.{u} @plInv_holds.{u} @hopDeep_holds.{u}`.
-/
theorem hopEx_holds : HopEx.{u} := @pHopEx.{u} @plInv_holds.{u} @hopDeep_holds.{u}

end UpperTheory.Gal.G3
