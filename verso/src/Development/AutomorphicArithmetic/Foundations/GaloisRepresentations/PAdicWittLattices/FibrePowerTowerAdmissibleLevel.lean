import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PNuInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSysOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAdmOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNCong
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateDiff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateTwist
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFullOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelArith
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTatePull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsogFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMapOfIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOrbit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransFree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGenSm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPowSm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.GObjMapCast
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtOrbit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitUniq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitCart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitForget
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitDeep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PDescMap
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitFree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMemOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKSNice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.ExistsDeeperNormalLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds

open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

/- English proof (translation)
The claim follows from `@pNuInt`.
-/
theorem nuInt_holds : NuInt := @pNuInt

/- English proof (translation)
The claim follows from `@pMultBasic @nuInt_holds`.
-/
theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

/- English proof (translation)
The claim follows from `@pKNBasic`.
-/
theorem kNBasic_holds : KNBasic := @pKNBasic

/- English proof (translation)
The claim follows from `@pSysOf @nuInt_holds`.
-/
theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

/- English proof (translation)
The claim follows from `@pAdmOf`.
-/
theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

/- English proof (translation)
The claim follows from `@pKNCong`.
-/
theorem kNCong_holds : KNCong := @pKNCong

/- English proof (translation)
The claim follows from `@pGSimOf @multBasic_holds`.
-/
theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

/- English proof (translation)
The claim follows from `@pRelComp`.
-/
theorem relComp_holds : RelComp := @pRelComp

/- English proof (translation)
The claim follows from `@pTateDiff`.
-/
theorem tateDiff_holds : TateDiff := @pTateDiff

/- English proof (translation)
The claim follows from `@pTateTwist @gSimOf_holds`.
-/
theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

/- English proof (translation)
The claim follows from `@pFullOf`.
-/
theorem fullOf_holds : FullOf := @pFullOf

/- English proof (translation)
The claim follows from `@pRelArith`.
-/
theorem relArith_holds : RelArith := @pRelArith

/- English proof (translation)
The claim follows from `@pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds`.
-/
theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

/- English proof (translation)
The claim follows from `@pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds`.
-/
theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

/- English proof (translation)
The claim follows from `@pHomPull`.
-/
theorem homPull_holds : HomPull := @pHomPull

/- English proof (translation)
The claim follows from `@pTatePull`.
-/
theorem tatePull_holds : TatePull := @pTatePull

/- English proof (translation)
The claim follows from `@pTransPull @homPull_holds @tatePull_holds`.
-/
theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

/- English proof (translation)
The claim follows from `@pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds`.
-/
theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

/- English proof (translation)
The claim follows from `@pRigid`.
-/
theorem rigid_holds : Rigid := @pRigid

/- English proof (translation)
The claim follows from `@pIsogFEt`.
-/
theorem isogFEt_holds : IsogFEt := @pIsogFEt

/- English proof (translation)
The claim follows from `@pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds`.
-/
theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

/- English proof (translation)
The claim follows from `@pPolUniq`.
-/
theorem polUniq_holds : PolUniq := @pPolUniq

/- English proof (translation)
The claim follows from `@pMapOfIso`.
-/
theorem mapOfIso_holds : MapOfIso := @pMapOfIso

/- English proof (translation)
The claim follows from `@pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds`.
-/
theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

/- English proof (translation)
The claim follows from `@pTransIso @isoPts_holds @isogFEt_holds`.
-/
theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

/- English proof (translation)
The claim follows from `@pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds`.
-/
theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

/- English proof (translation)
The claim follows from `@pTransFree @kNCong_holds`.
-/
theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

/- English proof (translation)
The claim follows from `@pGenSm`.
-/
theorem genSm_holds : GenSm := @pGenSm

/- English proof (translation)
The claim follows from `@pPowSm @genSm_holds`.
-/
theorem powSm_holds : PowSm := @pPowSm @genSm_holds

/- English proof (translation)
The claim follows from `@pEtDesc @extPts_holds`.
-/
theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

/- English proof (translation)
The claim follows from `@pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds`.
-/
theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

/- English proof (translation)
The claim follows from `@pWitComp @transSelf_holds @transComp_holds @transPull_holds`.
-/
theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

/- English proof (translation)
The claim follows from `@pWitCart @transIso_holds`.
-/
theorem witCart_holds : WitCart := @pWitCart @transIso_holds

/- English proof (translation)
The claim follows from `@pWitForget @mapOfIso_holds @transSelf_holds`.
-/
theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

/- English proof (translation)
The claim follows from `@pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds`.
-/
theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

/- English proof (translation)
The claim follows from `@pHomDesc @etDesc_holds`.
-/
theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

/- English proof (translation)
The claim follows from `@pPolDesc`.
-/
theorem polDesc_holds : PolDesc := @pPolDesc

/- English proof (translation)
The claim follows from `@pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds`.
-/
theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

/- English proof (translation)
The claim follows from `@pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds`.
-/
theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

/- English proof (translation)
The claim follows from `@pTwFEt @fEtBasic_holds @twGal_holds`.
-/
theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

/- English proof (translation)
The claim follows from `@pSigmaFEt`.
-/
theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt

/- English proof (translation)
The claim follows from `@pTwMem.{u} @splitsPts_holds @ptsOfSplits_holds @sigmaFEt_holds @twFEt_holds @twSplit_holds`.
-/
theorem twMem_holds : TwMem.{u} := @pTwMem.{u} @splitsPts_holds @ptsOfSplits_holds @sigmaFEt_holds @twFEt_holds @twSplit_holds

/- English proof (translation)
The claim follows from `@pSumFn.{u}`.
-/
theorem sumFn_holds : SumFn.{u} := @pSumFn.{u}

/- English proof (translation)
The claim follows from `@pMemOp.{u} @kNBasic_holds @plInv_holds.{u} @hopDeep_holds.{u} @hopEx_holds.{u} @twMem_holds.{u} @sumFn_holds.{u}`.
-/
theorem memOp_holds : MemOp.{u} := @pMemOp.{u} @kNBasic_holds @plInv_holds.{u} @hopDeep_holds.{u} @hopEx_holds.{u} @twMem_holds.{u} @sumFn_holds.{u}

/- English proof (translation)
The claim follows from `@pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds`.
-/
theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

/- English proof (translation)
The claim follows from `@pQuotUniq @etDesc_holds`.
-/
theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

/- English proof (translation)
The claim follows from `@pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds`.
-/
theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

/- English proof (translation)
The claim follows from `@pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds`.
-/
theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

/- English proof (translation)
The claim follows from `@pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds`.
-/
theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

/- English proof (translation)
The claim follows from `@pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds`.
-/
theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

/- English proof (translation)
The claim follows from `@pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds`.
-/
theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

/- English proof (translation)
The claim follows from `@pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds`.
-/
theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

/- English proof (translation)
The claim follows from `@pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds`.
-/
theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

/- English proof (translation)
The claim follows from `@pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds`.
-/
theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

/- English proof (translation)
The claim follows from `@pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds`.
-/
theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
