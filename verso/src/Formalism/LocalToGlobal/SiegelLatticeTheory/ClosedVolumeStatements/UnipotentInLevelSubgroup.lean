import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FormHermitianPositive
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdBlocks
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHFinOrd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.VanishNConj
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.LsSetresAvgW
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfG
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLeaf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDensePf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RightInvOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipFinal
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LieAveraging.NonRelCharCHolds

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.Pf Formalism.L2.SG.TermOp.Vanish

namespace Formalism.L2.SG.Closed

section Steps

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PsiDd_holds : Formalism.L2.SG.Pf.PsiDd X := Formalism.L2.SG.Pf.psiDd_holds X
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unipotent_in_level_subgroup : Formalism.L2.SG.PoincareInHH.Cut.UnipotentConjugateInLevel X u := Formalism.L2.SG.Pf.Level.unipotent_in_level_of_psi (PsiDd_holds X)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RatLevi_holds : Formalism.L2.SG.PoincareInHH.Cut.RatLevi X u := Formalism.L2.SG.Pf.ratLevi_holds X u
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem KsetSplit_holds : Formalism.L2.SG.PoincareInHH.Cut.KsetSplit X u := Formalism.L2.SG.Pf.ksetSplit_holds X u
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NeatKu_holds (hK : X.LevelSubgroupCharacter) : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK := Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu (X := X) (u := u) (hK := hK)
  (hL := Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X u) (hU := Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X u hK)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LatInj_holds : Formalism.L2.SG.Pf.LatInj X u := Formalism.L2.SG.Pf.latInj X u
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LatRowLat_holds : Formalism.L2.SG.Pf.LatRowLat X u := Formalism.L2.SG.Pf.latRowLat X u

end Steps

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem HFiniteC_holds : HFiniteC := fun _ X u => Formalism.L2.SG.Pf.hFinite_holds X u
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nilradical_conj_level : NilradicalConjLevel := Formalism.L2.SG.Pf.nilradical_conj_level'
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChiTrivialC_holds : ChiTrivialC := Formalism.L2.SG.Pf.chiTrivialC_outright
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AvgCore_holds : AvgCore := Formalism.L2.SG.TermOp.Vanish.avgCore
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TRExistsC_holds : TRExistsC := Formalism.L2.SG.Pf.trExistsC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SlabCoverC_holds : Formalism.L2.SG.Pf.Slab.SlabCoverC :=
  Formalism.L2.SG.Pf.SlabCoverPf.slab_covering_of_strong_approx Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation nilradical_conj_level
    (fun _ X u => RatLevi_holds X u) (fun _ X => PsiDd_holds X)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem KExpansionC_holds : KExpansionC :=
  Formalism.L2.SG.Pf.kExpansionC_holds_of SlabCoverC_holds Formalism.L2.SG.Pf.RegroupPf.regroupC_all
    (fun _ X Y u => NeatKu_holds X u Y.hK) (fun _ X => Formalism.L2.SG.Pf.fundBridge_holds X)
    (fun _ X u hK => Formalism.L2.SG.Pf.pserMeas_holds X u hK)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PuLinearC_holds : PuLinearC := Formalism.L2.SG.Pf.puLinearC

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FundExistsC_holds : FundExistsC := Formalism.L2.SG.Pf.fundExistsC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChiNIndepC_holds : ChiNIndepC := Formalism.L2.SG.NormCut.chiNIndepC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OOFundIndepC_holds : OOFundIndepC := Formalism.L2.SG.Pf.ooFundIndepC_of_nconj Formalism.L2.SG.Pf.nilradical_conj_level'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AmpWellDefC_holds : AmpWellDefC := Formalism.L2.SG.Pf.ampWellDefC_of_nconj Formalism.L2.SG.Pf.nilradical_conj_level'

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VolPosC_holds : VolPosC := Formalism.L2.SG.Pf.volPosC_of'' Formalism.L2.SG.Pf.noCofiniteC_holds HFiniteC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LemmaVC_holds : LemmaVC := Formalism.L2.SG.Pf.lemmaVC_of_rest Formalism.L2.SG.TermOp.Vanish.avgCore Formalism.L2.SG.TermOp.Vanish.rational_cocompact_holds
  Formalism.L2.SG.NonRelPf.nonRelCharC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OOIntAllC_holds (h : Formalism.L2.SG.Pf.OOLintSumC) : OOIntAllC := Formalism.L2.SG.Pf.ooIntAllC_holds_of h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AbsConvC_holds (h : Formalism.L2.SG.Pf.OOLintSumC) : AbsConvC := Formalism.L2.SG.Pf.absConvC_holds_of h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FoldOKC_holds (hFL : Formalism.L2.SG.Pf.FinLeviC) : FoldOKC :=
  Formalism.L2.SG.Pf.foldOKC_holds_of (fun _ X u => KsetSplit_holds X u) (fun _ X u => unipotent_in_level_subgroup X u)
    (fun _ X u => RatLevi_holds X u) Formalism.L2.SG.Pf.psiProd_all
    (Formalism.L2.SG.Pf.iUnfoldAll_of hFL Formalism.L2.SG.Pf.noCocompactC_holds Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem InHHC_holds : InHHC := Formalism.L2.SG.Pf.inHHC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FullExists_holds (hLoc : LocC) : FullExists := Formalism.L2.SG.Pf.fullExists_of_TR_Loc TRExistsC_holds hLoc

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem NeatC_holds : Formalism.L2.SG.TermOp.IdBlocks.NeatC := fun _ X Y u => NeatKu_holds X u Y.hK

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IdCellDiagC_holds : IdCellDiagC :=
  Formalism.L2.SG.Pf.idCellDiagC_of_steps3 Formalism.L2.SG.Pf.nLamNinf_holds VolPosC_holds Formalism.L2.SG.Pf.idMeetOneC_holds
    Formalism.L2.SG.Pf.idMeetPhaseC_holds Formalism.L2.SG.Pf.idMeetVolC_holds NeatC_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IdCellOffC_holds (hC : Formalism.L2.SG.Pf.IdOffConjC) (hL : Formalism.L2.SG.Pf.IdOffLiftC) : IdCellOffC :=
  Formalism.L2.SG.Pf.idCellOffC_of_conjLift Formalism.L2.SG.Pf.nLamNinf_holds VolPosC_holds hC hL

end Formalism.L2.SG.Closed
