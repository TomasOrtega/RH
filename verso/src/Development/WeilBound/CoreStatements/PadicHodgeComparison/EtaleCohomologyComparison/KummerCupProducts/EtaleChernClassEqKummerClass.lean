import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.CupLeib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EvExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchClsCocycleSec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StExOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StUniq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StTopOfStCol
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUniqOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullCZsmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StairCupFirst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignCancel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeCupOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneSubPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBasicOpenOfIsUnitSub
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveCl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffIterateVerschiebung
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumToAcrTeichmuller
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLogUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NatDegreeLgLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorialAcr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AcrisZeroImageDividedPower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UntiltIterateSymmEpsilon
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdemMulEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineBC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwUgCompAlgebraMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobIdem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRoot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassUniqueOfLiftAndLog
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepBasic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepConcOfInputs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEvCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepOp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompOfCechPt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LineMapExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChernClassCompatibleSystem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleSubfaceZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResGenRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedRootOfRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLCRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecResMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapNsmulTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsKumPow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecMapRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EdgeUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedResMor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecPairApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KapOneEqTwGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleChernClassEqKummerClass
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PowDivPowSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullPullOfPullC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeomPtGeomMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LcMorCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrimResZetaX
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VnRed
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernClassFamily

set_option backward.isDefEq.respectTransparency false

namespace CrystallineSemistableComparison.E.Main

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem inSch : InSch := GlobalTheory.EtC.sch_cls_cocycle_sec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stAdd : StAdd := GlobalTheory.CompanionTheory.StairAdd.stAdd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stCol : StCol := GlobalTheory.CompanionTheory.EdgeStair.stCol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stEx : StEx := GlobalTheory.CompanionTheory.EdgeStair.stEx_of_stCol stCol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stUniq : StUniq := GlobalTheory.CompanionTheory.EdgeStair.stUniq stCol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stTop : StTop := GlobalTheory.CompanionTheory.EdgeMap.stTop_of_stCol stCol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem edgeUniq : EdgeUniq := GlobalTheory.CompanionTheory.EdgeClass.edgeUniq_of stCol stAdd stUniq

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem edgeMap : EdgeMap := GlobalTheory.CompanionTheory.EdgeMapPull.edgeMap

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stCupA : StCupA := GlobalTheory.CompanionTheory.StairCupFirst.stCupA cupLeib

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stCupB : StCupB := GlobalTheory.CompanionTheory.Staircase.stCupB cupLeib stCol

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem edgeCup : EdgeCup := GlobalTheory.CompanionTheory.EdgeMap.edgeCup_of_steps cupCls stTop stCupA stCupB

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcCover : LcCover := GlobalTheory.CompanionTheory.LcCoverProof.lcCover

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem locSplit : LocSplit := GlobalTheory.CompanionTheory.LocSplitProof.locSplit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem primAlg : PrimAlg := GlobalTheory.CompanionTheory.PrimAlgProof.primAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootPow : RootPow := GlobalTheory.CompanionTheory.RootPowLC.rootPow primAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootsEx : RootsEx := GlobalTheory.CompanionTheory.RootsC.rootsEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcIdem : LcIdem := GlobalTheory.CompanionTheory.TiltIdem.lcIdem

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcSpec : LcSpec := GlobalTheory.CompanionTheory.LcSp.lcSpec_of_lcIdem lcIdem

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcNat : LcNat := GlobalTheory.CompanionTheory.LcNatProof.lcNat lcIdem lcSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logEx : LogEx := GlobalTheory.CompanionTheory.CrisLog.logEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logAlg : LogAlg := GlobalTheory.CompanionTheory.LogAlgPf.logAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logMul : LogMul := GlobalTheory.CompanionTheory.LogMulPf.logMul logAlg logEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem logEps : LogEps := GlobalTheory.CompanionTheory.LogEpsP.logEps

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem epsRoot : EpsRoot := GlobalTheory.CompanionTheory.EpsRootProof.epsRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lcLog : LcLog := GlobalTheory.CompanionTheory.LcLogProof.lcLog lcIdem lcSpec lcCover logEx logMul logEps epsRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineBC : LineBC := GlobalTheory.CompanionTheory.LineBase.lineBC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twUg : TwUg := GlobalTheory.CompanionTheory.TwUg.twUg_prop

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fPhi : FPhi := GlobalTheory.CompanionTheory.FrobLc.fPhi

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fKum : FKum := GlobalTheory.CompanionTheory.FKum.fKum rootPow lcLog

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem liftEx : LiftEx := GlobalTheory.CompanionTheory.LineLift.liftEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem firstChern_unique : FirstChernUniqueEtale := GlobalTheory.CompanionTheory.EtChern.chern_class_unique_of_lift_and_log liftEx logEx

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repBasic : RepBasic := GlobalTheory.CompanionTheory.EtEdge.repBasic evExt evNat inSch

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repConc : RepConc := GlobalTheory.CompanionTheory.EdgeMap.repConc_of_inputs evExt inSch repBasic

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repCup : RepCup := GlobalTheory.CompanionTheory.EdgeRep.repCup evExt evNat repBasic repConc inSch

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repOp : RepOp := GlobalTheory.CompanionTheory.EdgeRep.repOp evNat repConc repBasic

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resLoc : ResLoc := GlobalTheory.CompanionTheory.EdgeMap.resLoc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resZero : ResZero := GlobalTheory.CompanionTheory.EtRes.resZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cechPt : CechPt := GlobalTheory.CompanionTheory.CechPts.cechPt_spec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lineMap : LineMap := GlobalTheory.CompanionTheory.CechLine.lineMap_exists cechPt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem chern_class_compatible_system : FirstChernCompatibleSystem := GlobalTheory.CompanionTheory.ChernSys.chern_class_compatible_system cechPt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem firstChern_primitive_kummer : FirstChernCoboundary := GlobalTheory.CompanionTheory.KummerPrimitive.main evExt evNat evDel repConc repBasic cechPt

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resSplit : ResSplit := GlobalTheory.CompanionTheory.ResSplitProof.resSplit resLoc locSplit lcCover

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repRoot : RepRoot := GlobalTheory.CompanionTheory.EtRoot.repRoot repConc resZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redRoot : RedRoot := GlobalTheory.CompanionTheory.EdgeMap.redRoot_of_rep repRoot repOp repConc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twZero : TwZero := GlobalTheory.CompanionTheory.TwZeroGen.twZero rootPow lcCover repRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapSpec : KapSpec := GlobalTheory.CompanionTheory.KapSpecProof.kapSpec lcCover repRoot

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapBij : KapBij := GlobalTheory.CompanionTheory.KapBij.kapBij lcCover repRoot kapSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapMul : KapMul := GlobalTheory.CompanionTheory.KapMulE.kapMul_of lcCover repRoot kapSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapRed : KapRed := GlobalTheory.CompanionTheory.CstE.KapRedP.kapRed lcCover repRoot kapSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kumPow : KumPow := GlobalTheory.CompanionTheory.KumPowProof.kumPow lcCover repRoot kapSpec primAlg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resGood : ResGood := GlobalTheory.CompanionTheory.EdgeRes.resGood kapSpec kapBij resZero resSplit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etSpec : EtSpec := GlobalTheory.CompanionTheory.EtSpecProof.etSpec resGood stEx edgeUniq repBasic resZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etNat : EtNat := GlobalTheory.CompanionTheory.EtNatProof.etNat etSpec edgeMap repBasic kapSpec twZero

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etRed : EtRed := GlobalTheory.CompanionTheory.EdgeRed.etRed etSpec edgeMap repBasic repOp kapSpec kapRed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etCup : EtCup := GlobalTheory.CompanionTheory.EdgeProduct.etCup etSpec resGood edgeCup repBasic repCup kapMul

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etRoot : EtRoot := GlobalTheory.CompanionTheory.EdgeRoot.etRoot_of_spec etSpec repRoot kapSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etale_chern_class_eq_kummer_class : EtaleFirstChernKummer := GlobalTheory.CompanionTheory.EtaleChernClass.etale_chern_class_eq_kummer_class etSpec resGood stCol firstChern_primitive_kummer kumPow

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fRed : FRed := GlobalTheory.CompanionTheory.EtReduction.fred_of_etRed etRed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fEqui : FEqui := GlobalTheory.CompanionTheory.FEquiProof.fEqui etNat twUg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fNat : FNat := GlobalTheory.CompanionTheory.FNatProof.fNat etNat

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fRes : FRes := GlobalTheory.CompanionTheory.FResProof.fRes etNat

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fCup : FCup := GlobalTheory.CompanionTheory.EtCupF.fCup etCup morCup lcSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fRoot : FRoot := GlobalTheory.CompanionTheory.FRootCls.froot etRoot redRoot morCup lcSpec

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fUntw : FUntw := GlobalTheory.CompanionTheory.FUntwPf.main fCup fRoot cupOne

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem firstChern_family : FirstChernClassFamily := firstChern_family_of_lifts lineBC lineMap chern_class_compatible_system etale_chern_class_eq_kummer_class fKum fRes fUntw

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etale_comparison_map : EtaleComparisonMapExists := etale_comparison_map_of_facts rootsEx lcNat fRed fEqui fPhi fNat fCup fRoot firstChern_family

end CrystallineSemistableComparison.E.Main
