import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MWModEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MValPtsX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ResSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRankN
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecCard
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MObjTri
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPairCalc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullIsog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.UEltOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DivCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTorsFree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAdjoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerFromU
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsoOfKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MConstSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.TensorDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecSurj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecEquiv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MGrCard
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPowExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MGenDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdReadOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MAlgOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftFF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLineC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PowSuccSubMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFFRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRedPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKillLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSplitAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.ExistsAlg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MImgEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCaseE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRingHomog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCotanOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepHomog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SpMapAlgComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobPass
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepOfFF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTanOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobHom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPicFrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MQuasiInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobIsog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsogComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCaseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.EwOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCorrBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdEmb
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLevPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MEtInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MOrdKSE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MUKerW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIdealSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLevPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjEEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProdHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCountIn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCountOut

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
The claim follows from `wModEx_of`.
-/
theorem wModEx_holds  : WModEx := wModEx_of
/- English proof (translation)
The claim follows from `valPtsX_of`.
-/
theorem valPtsX_holds  : ValPtsX := valPtsX_of
/- English proof (translation)
The claim follows from `wVal_of valPtsX_holds`.
-/
theorem wVal_holds  : WVal := wVal_of valPtsX_holds
/- English proof (translation)
The claim follows from `rankN_of wVal_holds`.
-/
theorem rankN_holds  : RankN := rankN_of wVal_holds
/- English proof (translation)
The claim follows from `secCard_of`.
-/
theorem secCard_holds  : SecCard := secCard_of
/- English proof (translation)
The claim follows from `objTri_of`.
-/
theorem objTri_holds  : ObjTri := objTri_of
/- English proof (translation)
The claim follows from `pairCalc_of`.
-/
theorem pairCalc_holds  : PairCalc := pairCalc_of
/- English proof (translation)
The claim follows from `pullIsog_of`.
-/
theorem pullIsog_holds  : PullIsog := pullIsog_of
/- English proof (translation)
The claim follows from `pullKer_of`.
-/
theorem pullKer_holds  : PullKer := pullKer_of
/- English proof (translation)
The claim follows from `pulledEx_of objTri_holds pullIsog_holds pullKer_holds`.
-/
theorem pulledEx_holds  : PulledEx := pulledEx_of objTri_holds pullIsog_holds pullKer_holds
/- English proof (translation)
The claim follows from `pulledRead_of pullKer_holds`.
-/
theorem pulledRead_holds  : PulledRead := pulledRead_of pullKer_holds
/- English proof (translation)
The claim follows from `uElt_of`.
-/
theorem uElt_holds  : UElt := uElt_of
/- English proof (translation)
The claim follows from `divC_of`.
-/
theorem divC_holds  : DivC := divC_of
/- English proof (translation)
The claim follows from `torsFree_of divC_holds`.
-/
theorem torsFree_holds  : TorsFree := torsFree_of divC_holds
/- English proof (translation)
The claim follows from `adjoint_of pairCalc_holds torsFree_holds`.
-/
theorem adjoint_holds  : Adjoint := adjoint_of pairCalc_holds torsFree_holds
/- English proof (translation)
The claim follows from `kerFromU_of uElt_holds pairCalc_holds adjoint_holds divC_holds`.
-/
theorem kerFromU_holds  : KerFromU := kerFromU_of uElt_holds pairCalc_holds adjoint_holds divC_holds
/- English proof (translation)
The claim follows from `isoOfKer_of pairCalc_holds adjoint_holds divC_holds torsFree_holds`.
-/
theorem isoOfKer_holds  : IsoOfKer := isoOfKer_of pairCalc_holds adjoint_holds divC_holds torsFree_holds
/- English proof (translation)
The claim follows from `secInj_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds`.
-/
theorem secInj_holds  : SecInj := secInj_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds
/- English proof (translation)
The claim follows from `constSub_of`.
-/
theorem constSub_holds  : ConstSub := constSub_of
/- English proof (translation)
The claim follows from `oMod_of`.
-/
theorem oMod_holds  : OMod := oMod_of
/- English proof (translation)
The claim follows from `secSurj_of constSub_holds oMod_holds h4 objTri_holds pullKer_holds`.
-/
theorem secSurj_holds (h4 : QuotObj) : SecSurj := secSurj_of constSub_holds oMod_holds h4 objTri_holds pullKer_holds
/- English proof (translation)
The claim follows from `secEquiv_of wVal_holds rankN_holds valPtsX_holds secCard_holds secInj_holds (secSurj_holds h4)`.
-/
theorem secEquiv_holds (h4 : QuotObj) : SecEquiv := secEquiv_of wVal_holds rankN_holds valPtsX_holds secCard_holds secInj_holds (secSurj_holds h4)
/- English proof (translation)
The claim follows from `grCard_of`.
-/
theorem grCard_holds  : GrCard := grCard_of
/- English proof (translation)
The claim follows from `powExt_of`.
-/
theorem powExt_holds  : PowExt := powExt_of
/- English proof (translation)
The claim follows from `genDown_of`.
-/
theorem genDown_holds  : GenDown := genDown_of
/- English proof (translation)
The claim follows from `resClosed_of`.
-/
theorem resClosed_holds  : ResClosed := resClosed_of
/- English proof (translation)
The claim follows from `ordReadOf_of countIn_of countOut_of`.
-/
theorem ordReadOf_holds  : OrdReadOf := ordReadOf_of countIn_of countOut_of
/- English proof (translation)
The claim follows from `algOf_of`.
-/
theorem algOf_holds  : AlgOf := algOf_of
/- English proof (translation)
The claim follows from `liftPt_of`.
-/
theorem liftPt_holds  : LiftPt := liftPt_of
/- English proof (translation)
The claim follows from `liftFF_of algOf_holds liftPt_holds`.
-/
theorem liftFF_holds  : LiftFF := liftFF_of algOf_holds liftPt_holds
/- English proof (translation)
The claim follows from `lineC_of rankN_holds liftFF_holds`.
-/
theorem lineC_holds  : LineC := lineC_of rankN_holds liftFF_holds
/- English proof (translation)
The claim follows from `kerU_of uElt_holds`.
-/
theorem kerU_holds  : KerU := kerU_of uElt_holds
/- English proof (translation)
The claim follows from `fFRead_of algOf_holds`.
-/
theorem fFRead_holds  : FFRead := fFRead_of algOf_holds
/- English proof (translation)
The claim follows from `kerRead_of kerU_holds fFRead_holds liftFF_holds pullKer_holds wVal_holds`.
-/
theorem kerRead_holds  : KerRead := kerRead_of kerU_holds fFRead_holds liftFF_holds pullKer_holds wVal_holds
/- English proof (translation)
The claim follows from `redPts_of`.
-/
theorem redPts_holds  : RedPts := redPts_of
/- English proof (translation)
The claim follows from `killLocal_of`.
-/
theorem killLocal_holds  : KillLocal := killLocal_of
/- English proof (translation)
The claim follows from `splitAlg_of`.
-/
theorem splitAlg_holds  : SplitAlg := splitAlg_of
/- English proof (translation)
The claim follows from `infE_of splitAlg_holds`.
-/
theorem infE_holds  : InfE := infE_of splitAlg_holds
/- English proof (translation)
The claim follows from `sameE_of killLocal_holds infE_holds`.
-/
theorem sameE_holds  : SameE := sameE_of killLocal_holds infE_holds
/- English proof (translation)
The claim follows from `imgEq_of objTri_holds`.
-/
theorem imgEq_holds  : ImgEq := imgEq_of objTri_holds
/- English proof (translation)
The claim follows from `caseE_of sameE_holds kerU_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds`.
-/
theorem caseE_holds  : CaseE := caseE_of sameE_holds kerU_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
/- English proof (translation)
The claim follows from `ringHomog_of`.
-/
theorem ringHomog_holds  : RingHomog := ringHomog_of
/- English proof (translation)
The claim follows from `cotanOne_of`.
-/
theorem cotanOne_holds  : CotanOne := cotanOne_of
/- English proof (translation)
The claim follows from `chainLoc_of`.
-/
theorem chainLoc_holds  : ChainLoc := chainLoc_of
/- English proof (translation)
The claim follows from `chainRing_of chainLoc_holds`.
-/
theorem chainRing_holds  : ChainRing := chainRing_of chainLoc_holds
/- English proof (translation)
The claim follows from `repHomog_of`.
-/
theorem repHomog_holds  : RepHomog := repHomog_of
/- English proof (translation)
The claim follows from `frobRing_of`.
-/
theorem frobRing_holds  : FrobRing := frobRing_of
/- English proof (translation)
The claim follows from `infW_of ringHomog_holds cotanOne_holds chainRing_holds repHomog_holds frobRing_holds`.
-/
theorem infW_holds  : InfW := infW_of ringHomog_holds cotanOne_holds chainRing_holds repHomog_holds frobRing_holds
/- English proof (translation)
The claim follows from `frobPass_of infE_holds`.
-/
theorem frobPass_holds  : FrobPass := frobPass_of infE_holds
/- English proof (translation)
The claim follows from `repOfFF_of algOf_holds`.
-/
theorem repOfFF_holds  : RepOfFF := repOfFF_of algOf_holds
/- English proof (translation)
The claim follows from `tanOne_of uElt_holds`.
-/
theorem tanOne_holds  : TanOne := tanOne_of uElt_holds
/- English proof (translation)
The claim follows from `sameW_of killLocal_holds infW_holds frobPass_holds kerU_holds repOfFF_holds tanOne_holds`.
-/
theorem sameW_holds  : SameW := sameW_of killLocal_holds infW_holds frobPass_holds kerU_holds repOfFF_holds tanOne_holds
/- English proof (translation)
The claim follows from `frobHom_of`.
-/
theorem frobHom_holds  : FrobHom := frobHom_of
/- English proof (translation)
The claim follows from `frobFin_of`.
-/
theorem frobFin_holds  : FrobFin := frobFin_of
/- English proof (translation)
The claim follows from `picFrob_of`.
-/
theorem picFrob_holds  : PicFrob := picFrob_of
/- English proof (translation)
The claim follows from `quasiInv_of pairCalc_holds divC_holds`.
-/
theorem quasiInv_holds  : QuasiInv := quasiInv_of pairCalc_holds divC_holds
/- English proof (translation)
The claim follows from `frobIsog_of frobHom_holds frobFin_holds picFrob_holds quasiInv_holds`.
-/
theorem frobIsog_holds  : FrobIsog := frobIsog_of frobHom_holds frobFin_holds picFrob_holds quasiInv_holds
/- English proof (translation)
The claim follows from `isogComp_of pairCalc_holds`.
-/
theorem isogComp_holds  : IsogComp := isogComp_of pairCalc_holds
/- English proof (translation)
The claim follows from `caseW_of sameW_holds frobIsog_holds isogComp_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds`.
-/
theorem caseW_holds  : CaseW := caseW_of sameW_holds frobIsog_holds isogComp_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
/- English proof (translation)
The claim follows from `ew_of wModEx_holds rankN_holds lineC_holds (secEquiv_holds h4) kerRead_holds redPts_holds countIn_of pulledEx_holds caseE_holds caseW_holds`.
-/
theorem eW_holds (h4 : QuotObj) : EW := ew_of wModEx_holds rankN_holds lineC_holds (secEquiv_holds h4) kerRead_holds redPts_holds countIn_of pulledEx_holds caseE_holds caseW_holds
/- English proof (translation)
The claim follows from `corrBC_of wModEx_holds rankN_holds (secEquiv_holds h4) grCard_holds`.
-/
theorem corrBC_holds (h4 : QuotObj) : CorrBC := corrBC_of wModEx_holds rankN_holds (secEquiv_holds h4) grCard_holds
/- English proof (translation)
The claim follows from `ordEmb_of h3 genDown_holds resClosed_holds ordReadOf_holds (eW_holds h4)`.
-/
theorem ordEmb_holds (h3 : OrdGen) (h4 : QuotObj) : OrdEmb := ordEmb_of h3 genDown_holds resClosed_holds ordReadOf_holds (eW_holds h4)
/- English proof (translation)
The claim follows from `levPull_of pullKer_holds`.
-/
theorem levPull_holds  : LevPull := levPull_of pullKer_holds
/- English proof (translation)
The claim follows from `etInj_of objTri_holds levPull_holds`.
-/
theorem etInj_holds  : EtInj := etInj_of objTri_holds levPull_holds
/- English proof (translation)
The claim follows from `ordKSE_of (corrBC_holds h4) (ordEmb_holds h3 h4) powExt_holds etInj_holds`.
-/
theorem ordKSE_holds (h3 : OrdGen) (h4 : QuotObj) : OrdKSE := ordKSE_of (corrBC_holds h4) (ordEmb_holds h3 h4) powExt_holds etInj_holds
/- English proof (translation)
The claim follows from `tjExF_of h1 h2 objTri_holds pullIsog_holds pullKer_holds`.
-/
theorem tjExF_holds (h1 : EsNorm) (h2 : EsGen) : TjExF := tjExF_of h1 h2 objTri_holds pullIsog_holds pullKer_holds
/- English proof (translation)
The claim follows from `uKerW_of kerU_holds pullKer_holds`.
-/
theorem uKerW_holds  : UKerW := uKerW_of kerU_holds pullKer_holds
/- English proof (translation)
The claim follows from `idealSplit_of`.
-/
theorem idealSplit_holds  : IdealSplit := idealSplit_of
/- English proof (translation)
The claim follows from `levPush_of idealSplit_holds`.
-/
theorem levPush_holds  : LevPush := levPush_of idealSplit_holds
/- English proof (translation)
The claim follows from `tjEEx_of objTri_holds pulledEx_holds pullKer_holds uKerW_holds levPull_holds levPush_holds`.
-/
theorem tjEEx_holds  : TjEEx := tjEEx_of objTri_holds pulledEx_holds pullKer_holds uKerW_holds levPull_holds levPush_holds
/- English proof (translation)
The claim follows from `congKS_of (tjExF_holds h1 h2) tjEEx_holds (ordKSE_holds h3 h4) ptIdOfOrd_holds`.
-/
theorem congKS_holds (h1 : EsNorm) (h2 : EsGen) (h3 : OrdGen) (h4 : QuotObj) : CongKS :=
  congKS_of (tjExF_holds h1 h2) tjEEx_holds (ordKSE_holds h3 h4) ptIdOfOrd_holds

end UpperTheory.Gal.crystallineComparison.Mod
