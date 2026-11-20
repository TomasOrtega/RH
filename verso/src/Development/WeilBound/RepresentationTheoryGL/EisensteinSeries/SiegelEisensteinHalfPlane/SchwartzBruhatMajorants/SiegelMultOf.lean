import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.ContinuousOnThetaCFunLtr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneAddInvPowMulRpowLe
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.TestFun
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.MirGen
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.SchwartzBruhatMajorants.SgOneHd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdentityTubeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeChainHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionLawHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightLipschitzHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StagedEstimateHoldsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WallLawOfSectionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeightsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GalleryOfTubesAndCrossingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferOfSectionAndWallLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistOfSectionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockDeterminantLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionLawStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLawOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviDecompOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviQuotientOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceGroupOfBlockDetStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelInductionFromGalleryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalTestFunctionExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierMirabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinMultiplicativityStatement
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFactorisationHolomorphic

noncomputable section

namespace PositivityTheory.RgEis.Hd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem idTube : IdTube := GlobalTheory.T.identity_tube_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tubeChain : TubeChain := GlobalTheory.T.tube_chain_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem secLaw : SecLaw := GlobalTheory.T.section_law_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem htLip : HtLip := GlobalTheory.T.height_lipschitz_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stage : PiLocalization₂ := GlobalTheory.T.staged_estimate_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wallLaw_of : SecLaw → WallLaw := GlobalTheory.T.wall_law_of_section_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cross_of : SecLaw → HtLip → PiLocalization₂ → WallLaw → Cross := GlobalTheory.T.crossing_of_walls_and_heights
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gallery_of : SecLaw → IdTube → TubeChain → Cross → Gallery := GlobalTheory.T.gallery_of_tubes_and_crossing
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transfer_of : SecLaw → WallLaw → Transfer := GlobalTheory.T.transfer_of_section_and_wall_laws
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twist_of : SecLaw → Twist := GlobalTheory.T.twist_of_section_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem scale : Scale := GlobalTheory.T.eisenstein_scaling_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem grpTop : GrpTop := GlobalTheory.T.general_linear_topological_group
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bdetLaw : BdetLaw := GlobalTheory.T.block_determinant_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extLaw : ExtLaw := GlobalTheory.T.extension_law
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parLaw_of : BdetLaw → ExtLaw → GrpTop → ParLaw := GlobalTheory.T.parabolic_law_of_block_det
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leviS_of : BdetLaw → ExtLaw → GrpTop → LeviS := GlobalTheory.T.levi_decomp_of_block_det
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem leviQ_of : BdetLaw → ExtLaw → GrpTop → LeviQ := GlobalTheory.T.levi_quotient_of_block_det
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem convGrOf_of : BdetLaw → ExtLaw → ConvGrOf := GlobalTheory.T.convergence_group_of_block_det
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem convU_of : ParLaw → ConvU := GlobalTheory.T.unipotent_convergence_of_parabolic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStep_of : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := GlobalTheory.T.siegel_induction_from_gallery
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem epConv : EpConv := GlobalTheory.CompanionTheory.EpConvB.epConv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem epMain_of : EpConv → EpMain := GlobalTheory.CompanionTheory.EpsteinMain.Hd.epMain_of_epConv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem testFun : TestFun := PositivityTheory.RgEis.TF.testFun
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem testSph : TestSph := GlobalTheory.T.spherical_test_function_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stdGood : StdGood := GlobalTheory.T.standard_section_good
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mirGen_of : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen := PositivityTheory.RgEis.MG.mirGen
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dict : Dict := GlobalTheory.T.local_global_dictionary
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dictInf : DictInf := GlobalTheory.T.archimedean_local_global_dictionary
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmGood_of : StdGood → Dict → DictInf → CMGood := GlobalTheory.T.constant_multiplier_good
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cmMir_of : Dict → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → MirGen → CMMir := GlobalTheory.T.constant_multiplier_mirabolic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgOne_of : SecLaw → WallLaw → Scale → StdGood → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw →
    MirGen → SgOne := PositivityTheory.RgEis.So.sgOne_hd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelMult_of : SecLaw → WallLaw → Dict → DictInf → CMGood → GrpTop → BdetLaw → ExtLaw → ParLaw → SgAll →
    SiegelEisensteinSeries.BRoad.SiegelMult := GlobalTheory.T.siegel_eisenstein_multiplicativity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem sgAll_of (hG : CMGood) (hM : CMMir) (h1 : SgOne) (hS : SgStep) : SgAll := by
  intro F E _ _ _ _ _ σ χ c h h' hχ hc ε
  suffices H : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → 1 ≤ n → (adCM σ χ).Sg ε ι from
    fun ι _ _ hι => H _ ι rfl hι
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ι _ _ hι hn
    rcases Nat.eq_or_lt_of_le hn with e | e
    · exact h1 F E σ χ c h h' hχ hc ε ι (hι.trans e.symm)
    · exact hS E _ (adCM σ χ) (hG F E σ χ c h h' hχ hc) (hM F E σ χ c h h' hχ hc) ε ι (by omega)
        fun κ _ _ h1 h2 => ih _ (hι ▸ h2) κ rfl h1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgAll : SgAll :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
    (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
    (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
      (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
      (convGrOf_of bdetLaw extLaw) (convU_of hP))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eisBL : GlobalTheory.ThK.Dbl.EisBL :=
  have hW := wallLaw_of secLaw
  have hP := parLaw_of bdetLaw extLaw grpTop
  have hG := cmGood_of stdGood dict dictInf
  have hM := mirGen_of secLaw stdGood bdetLaw epConv (epMain_of epConv) testFun testSph
  SiegelEisensteinSeries.BRoad.eisBL_of GlobalTheory.T.eisenstein_half_holds
    (siegelMult_of secLaw hW dict dictInf hG grpTop bdetLaw extLaw hP
      (sgAll_of hG (cmMir_of dict hG grpTop bdetLaw extLaw hP hM)
        (sgOne_of secLaw hW scale stdGood dict dictInf hG grpTop bdetLaw extLaw hP hM)
        (sgStep_of (gallery_of secLaw idTube tubeChain (cross_of secLaw htLip stage hW)) (transfer_of secLaw hW)
          (twist_of secLaw) grpTop hP (leviS_of bdetLaw extLaw grpTop) (leviQ_of bdetLaw extLaw grpTop)
          (convGrOf_of bdetLaw extLaw) (convU_of hP))))
    GlobalTheory.CompanionTheory.Entire.local_factorisation

end PositivityTheory.RgEis.Hd
