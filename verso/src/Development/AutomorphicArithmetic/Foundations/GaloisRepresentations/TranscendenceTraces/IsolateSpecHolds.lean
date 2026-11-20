import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PtExOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtCommon
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtPtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolate
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIsolateSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGenBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PIndDesc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSHSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFinSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImageFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinGeo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRingSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinAff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCoverOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PLocFinSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.WtBCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PInvTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PGalTrans
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitCover
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtClopen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountWt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtLocal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtCrit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormAff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtVanish
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtUnique
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtNormal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtDegConst
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNmlNoeth
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOfFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtDeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PStalkSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSumPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PArtSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultPt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PWtFlat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFunSec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrHlOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumNat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtInj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamSemi
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRedZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSecFun
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumExLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRpBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrIdQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDegQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrCompQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrBCQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEqQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCycComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.OpEqOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrBCQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PImgBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrCompQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.ImgcSpec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamBC
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrSplitQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrGraphQ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrPush
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.TrBCOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDeg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrRel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.FLOf

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptEx_holds : PtEx := @ptEx_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chart_holds : Chart := @chart_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fibFin_holds : FibFin := @fibFin_of @chart_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptCommon_holds : PtCommon := @ptCommon_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptOne_holds : PtOne := @ptOne_of @chart_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtExt_holds : WtExt := @wtExt_of @ptOne_holds @chart_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtPt_holds : WtPt := @wtPt_of @wtExt_holds @ptCommon_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptLift_holds : PtLift := @ptLift_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isolateSpec_holds : IsolateSpec := @isolateSpec_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isolate_holds : Isolate := @isolate_of @chart_holds @isolateSpec_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem imageOne_holds : ImageOne := @imageOne_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem genBasic_holds : GenBasic := @genBasic_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indDesc_holds : IndDesc := @indDesc_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sHSec_holds : SHSec := @sHSec_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finSec_holds : FinSec := @finSec_of @sHSec_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem imageFin_holds : ImageFin := @imageFin_of @imageOne_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ringSplit_holds : RingSplit := @ringSplit_of @finSec_holds @indDesc_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locFinAff_holds : LocFinAff := @locFinAff_of @chart_holds @ringSplit_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locFinGeo_holds : LocFinGeo := @locFinGeo_of @locFinAff_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem coverOne_holds : CoverOne := @coverOne_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locFinSec_holds : LocFinSec := @locFinSec_of @coverOne_holds @locFinGeo_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtBC_holds : WtBC := @wtBC_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invTrans_holds : InvTrans := @invTrans_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem galTrans_holds : GalTrans := @galTrans_of @invTrans_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem splitField_holds : SplitField := @splitField_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumComp_holds : SumComp := @sumComp_of @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtComp_holds : WtComp := @wtComp_of @sumComp_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem splitCover_holds : SplitCover := @splitCover_of @splitField_holds @galTrans_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtLin_holds : WtLin := @wtLin_of @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countEx_holds : CountEx := @countEx_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countWt_holds : CountWt := @countWt_of @ptEx_holds @ptLift_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtCrit_holds : WtCrit := @wtCrit_of @ptEx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtClopen_holds : WtClopen := @wtClopen_of @wtCrit_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem artSum_holds : ArtSum := @artSum_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stalkSum_holds : StalkSum := @stalkSum_of @chart_holds @artSum_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multSec_holds : MultSec := @multSec_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multSumPt_holds : MultSumPt := multSumPt_of stalkSum_holds multSec_holds ptLift_holds ptOne_holds fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multBC_holds : MultBC := @multBC_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multSum_holds : MultSum := @multSum_of @multSumPt_holds @multBC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multOpen_holds : MultOpen := @multOpen_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtFlat_holds : WtFlat := wtFlat_of wtClopen_holds multSum_holds multBC_holds multOpen_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multPt_holds : MultPt := @multPt_of @wtFlat_holds @wtPt_holds @multBC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normSpec_holds : NormSpec := normSpec_of splitCover_holds countEx_holds countWt_holds multPt_holds ptEx_holds ptLift_holds genBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtPush_holds : WtPush := @wtPush_of @sumComp_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtLocal_holds : WtLocal := @wtLocal_of @wtCrit_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normAff_holds : NormAff := @normAff_of @chart_holds @normSpec_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtOpen_holds : NwtOpen := @nwtOpen_of @wtBC_holds @multBC_holds @genBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtVanish_holds : WtVanish := wtVanish_of isolate_holds wtPt_holds ptEx_holds ptLift_holds fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtUnique_holds : WtUnique := @wtUnique_of @wtVanish_holds @wtLin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtAgree_holds : NwtAgree := nwtAgree_of nwtOpen_holds wtUnique_holds genBasic_holds multBC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtGlue_holds : NwtGlue := nwtGlue_of nwtAgree_holds wtLocal_holds multBC_holds genBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtNormal_holds : WtNormal := @wtNormal_of @normAff_holds @nwtGlue_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtDegConst_holds : WtDegConst := @wtDegConst_of @ptEx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nmlInt_holds : NmlInt := @nmlInt_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nmlNoeth_holds : NmlNoeth := @nmlNoeth_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nmlLoc_holds : NmlLoc := @nmlLoc_of @nmlInt_holds @nmlNoeth_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtFlat_holds : NwtFlat := nwtFlat_of wtBC_holds wtFlat_holds wtUnique_holds multBC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multEt_holds : MultEt := @multEt_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multBasic_holds : MultBasic := @multBasic_of @multBC_holds @multOpen_holds @multEt_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtOfFlat_holds : NwtOfFlat := @nwtOfFlat_of @wtFlat_holds @wtUnique_holds @genBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nwtDeg_holds : NwtDeg := nwtDeg_of wtNormal_holds wtDegConst_holds multSum_holds multBC_holds genBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funSec_holds : FunSec := @funSec_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phiEx_holds : PhiEx := @phiEx_of @locFinSec_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fL_holds : FL := @fL_of @phiEx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rpBasic_holds : RpBasic := @rpBasic_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem imgBasic_holds : ImgBasic := @imgBasic_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rpOp_holds : RpOp := @rpOp_of @imgBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opEq_holds : OpEq := @opEq_of @fL_holds @rpBasic_holds @rpOp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secFun_holds : SecFun := @secFun_of @ptEx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumExLoc_holds : SumExLoc := @sumExLoc_of @secFun_holds @funSec_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumNat_holds : SumNat := @sumNat_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptInj_holds : PtInj := @ptInj_of @ptEx_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumEx_holds : SumEx := @sumEx_of @sumExLoc_holds @sumNat_holds @ptInj_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trSum_holds : TrSum := trSum_of sumEx_holds sumNat_holds ptInj_holds fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trChar_holds : TrChar := @trChar_of @fL_holds @opEq_holds @trSum_holds @ptInj_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famSemi_holds : FamSemi := @famSemi_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redZero_holds : RedZero := @redZero_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trRed_holds (h : GlobalTheory.EtC.A8) : TrRed := trRed_of h trChar_holds trSum_holds opEq_holds famSemi_holds redZero_holds rpBasic_holds rpOp_holds ptInj_holds fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trHl_holds (h : GlobalTheory.EtC.A8) : TrHl := @trHl_of (@trRed_holds h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famLin_holds : FamLin := @famLin_of @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trLin_holds : TrLin := trLin_of trChar_holds famLin_holds wtLin_holds rpBasic_holds rpOp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trIdQ_holds (h : GlobalTheory.EtC.A8) : TrIdQ := @trIdQ_of (@trHl_holds h) @trLin_holds @wtLin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famPush_holds : FamPush := @famPush_of @sumComp_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trPush_holds : TrPush := trPush_of trChar_holds famPush_holds wtPush_holds rpBasic_holds rpOp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trDeg_holds : TrDeg := @trDeg_of @trPush_holds @trLin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trDegQ_holds (h : GlobalTheory.EtC.A8) : TrDegQ := @trDegQ_of (@trHl_holds h) @trDeg_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famComp_holds : FamComp := @famComp_of @sumComp_holds @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trComp_holds : TrComp := trComp_of trChar_holds famComp_holds wtComp_holds rpBasic_holds rpOp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trCompQ_holds (h : GlobalTheory.EtC.A8) : TrCompQ := trCompQ_of (trHl_holds h) trComp_holds wtComp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem famBC_holds : FamBC := @famBC_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trBC_holds : TrBC := trBC_of trChar_holds famBC_holds wtBC_holds rpBasic_holds rpOp_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trBCQ_holds (h : GlobalTheory.EtC.A8) : TrBCQ := trBCQ_of (trHl_holds h) trBC_holds wtBC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trRel_holds : TrRel := @trRel_of @trLin_holds @wtLin_holds @wtVanish_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corrEq_holds : CorrEq := corrEq_of imageFin_holds trRel_holds trPush_holds wtPush_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corrEqQ_holds (h : GlobalTheory.EtC.A8) : CorrEqQ := @corrEqQ_of (@trHl_holds h) @corrEq_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cycComp_holds : CycComp := @cycComp_of @fibFin_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corrBCQ_holds (h : GlobalTheory.EtC.A8) : CorrBCQ := @corrBCQ_of (@trBCQ_holds h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corrCompQ_holds (h : GlobalTheory.EtC.A8) : CorrCompQ := corrCompQ_of cycComp_holds wtBC_holds wtComp_holds (trBCQ_holds h) (trCompQ_holds h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem trSplitQ_holds (h : GlobalTheory.EtC.A8) : TrSplitQ := trSplitQ_of (trBCQ_holds h) (corrEqQ_holds h) (trIdQ_holds h) wtLin_holds wtFlat_holds multBasic_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem corrGraphQ_holds (h : GlobalTheory.EtC.A8) : CorrGraphQ := @corrGraphQ_of (@trIdQ_holds h) @wtLin_holds

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem weights_holds : Weights := ⟨wtBC_holds, wtComp_holds, wtLin_holds, wtPush_holds, wtPt_holds, wtUnique_holds, wtDegConst_holds,
    multBasic_holds, multSum_holds, wtFlat_holds, wtNormal_holds, nmlLoc_holds, nwtFlat_holds, nwtOfFlat_holds,
    nwtDeg_holds⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem torsion_holds : Torsion :=
  ⟨@trSum_holds, @trBC_holds, @trComp_holds, @trLin_holds, @trPush_holds, @trDeg_holds, @corrEq_holds⟩

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem adic_holds (h : GlobalTheory.EtC.A8) : Adic := ⟨trRed_holds h, trHl_holds h, trBCQ_holds h, trCompQ_holds h, trDegQ_holds h, corrEqQ_holds h, corrBCQ_holds h,
    corrCompQ_holds h, corrGraphQ_holds h, trSplitQ_holds h⟩

end UpperTheory.Gal.TranscendenceTraces
