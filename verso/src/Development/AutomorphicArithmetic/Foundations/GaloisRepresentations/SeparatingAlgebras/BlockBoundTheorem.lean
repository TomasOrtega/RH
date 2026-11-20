import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsCloseVectorUltrametric
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetLow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FixVec
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ExistsInvariantFlagModL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TriMat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDet
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CodimPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HSPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RFormula
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PairTerm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WtPosTermPos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MeanVal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensCont
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NullZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.InjAEPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DensSymm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.HalfCancel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RIntPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StarEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SymExPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmallPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaEig
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RepsEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Planch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Combine
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.Restrict
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.AlgCPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EigOfHasSat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SatExPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GlobOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NeglAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TestOp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CongSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TowerPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LocComm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RatFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllGrp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EllPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.WBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CoverPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.EqOneOfFinInf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PartFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfFinsetSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CountGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmoothAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenseGen
import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.ToPolyX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NormMapIntegerLeOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DenomBdd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TotalDegreeLeOfCol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SizeLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RhoBound
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LatFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LevelEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FrameW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.MaxCpt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PowNhds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.KerOpen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.CharSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TwistPart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TyStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DiscAHomog
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfSmul

namespace UpperTheory.Gal.Gen

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hB_holds : HB := hB_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem detLow_holds : DetLow := detLow_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fixVec_holds : FixVec := fixVec_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem flag_holds : Flag := flag_pf fixVec_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem triMat_holds : TriMat := triMat_pf flag_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem groupDet_holds : GroupDet := groupDet_pf triMat_holds detLow_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem alg_holds : Alg := alg_pf hB_holds groupDet_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem codim_holds : Codim := codim_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hS_holds : HS := hS_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rFormula_holds : RFormula := rFormula_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rConj_holds : RConj := rConj_pf rFormula_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wtPos_holds : WtPos := wtPos_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem meanVal_holds : MeanVal := meanVal_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem densCont_holds : DensCont := densCont_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfInt_holds : HalfInt := halfInt_pf wtPos_holds meanVal_holds densCont_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nullZero_holds : NullZero := nullZero_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem injAE_holds : InjAE := injAE_pf nullZero_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem densSymm_holds : DensSymm := densSymm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rDens_holds : RDens := rDens_pf rFormula_holds densSymm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rInt_holds : RInt := rInt_pf injAE_holds rDens_holds halfInt_holds densCont_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem starEx_holds : StarEx := starEx_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem symEx_holds : SymEx := symEx_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem small_holds : Small := small_pf symEx_holds starEx_holds nullZero_holds densCont_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gammaEig_holds : GammaEig := gammaEig_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gammaInt_holds : GammaInt := gammaInt_pf rInt_holds densCont_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gammaConj_holds : GammaConj := gammaConj_pf rConj_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repsEx_holds : RepsEx := repsEx_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem planch_holds : Planch := planch_pf gammaInt_holds gammaConj_holds gammaEig_holds injAE_holds densCont_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem combine_holds : Combine := combine_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem restrict_holds : Restrict := restrict_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algC_holds : AlgC := algC_pf alg_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locOp_holds : LocOp := locOp_pf repsEx_holds planch_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem satEx_holds : SatEx := satEx_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem globOp_holds : GlobOp := globOp_pf locOp_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem neglAt_holds : NeglAt := neglAt_pf globOp_holds small_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem congSub_holds : CongSub := congSub_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tower_holds : Tower := tower_pf congSub_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levFacts_holds : LevFacts := levFacts_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locComm_holds : LocComm := locComm_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ratFin_holds : RatFin := ratFin_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellGrp_holds : EllGrp := ellGrp_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ell_holds : Ell := ell_pf ellGrp_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wBound_holds : WBound := wBound_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countCore_holds : CountCore := countCore_pf hS_holds wBound_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cover_holds : Cover := cover_pf levFacts_holds locComm_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sep_holds : Sep := sep_pf levFacts_holds locComm_holds ratFin_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem partFacts_holds : PartFacts := partFacts_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem count_holds : Count := count_pf countCore_holds cover_holds sep_holds partFacts_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem countGen_holds : CountGen := countGen_pf count_holds neglAt_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stepCore_holds : StepCore := stepCore_pf algC_holds codim_holds partFacts_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smoothAt_holds : SmoothAt := smoothAt_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem step_holds : Step := step_pf smoothAt_holds tower_holds levFacts_holds ell_holds countGen_holds stepCore_holds partFacts_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem denseGen_holds : DenseGen := denseGen_pf step_holds partFacts_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem toPolyX_holds : ToPolyX := toPolyX_pf partFacts_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kappa_holds : Kappa := kappa_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem denomBdd_holds : DenomBdd := denomBdd_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degLe_holds : DegLe := degLe_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blockBound_holds : BlockBound := blockBound_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem detBound_holds : DetBound := detBound_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sizeLe_holds : SizeLe := sizeLe_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rhoBound_holds : RhoBound := rhoBound_pf degLe_holds blockBound_holds detBound_holds sizeLe_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem latFacts_holds : LatFacts := latFacts_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levelEx_holds : LevelEx := levelEx_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frameW_holds : FrameW := frameW_pf kappa_holds denomBdd_holds rhoBound_holds latFacts_holds levelEx_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem maxCpt_holds : MaxCpt := maxCpt_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem powNhds_holds : PowNhds := powNhds_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kerOpen_holds : KerOpen := kerOpen_pf powNhds_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem charSum_holds : CharSum := charSum_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twistPart_holds : TwistPart := twistPart_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tyStep_holds : TyStep := tyStep_pf levFacts_holds ell_holds kerOpen_holds charSum_holds twistPart_holds

end UpperTheory.Gal.Gen
