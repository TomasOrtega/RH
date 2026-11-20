import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyContinuityFilteredColimitRings
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.StrictHenselizationStalkEquivOfColimitPresentati
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SimplicialChainsDegreeZeroInjective
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechLevelIsoSigmaIntersectionsOfCoprod
import Development.EtaleCohomology.EtaleSheaves.AdjoinRootExtension
import Development.EtaleCohomology.EtaleSheaves.AICSHPf
import Development.EtaleCohomology.EtaleSheaves.AffinePf
import Development.EtaleCohomology.EtaleSheaves.AlgResPropsPf
import Development.EtaleCohomology.EtaleSheaves.BasePf
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangePolynomialInductionOfLimit
import Development.EtaleCohomology.EtaleSheaves.CechSigmaOf
import Development.EtaleCohomology.EtaleSheaves.CechYoneda
import Development.EtaleCohomology.EtaleSheaves.CechSqPf
import Development.EtaleCohomology.EtaleSheaves.IntegralSurjectiveRingCechAugmentationEtaleEqv
import Development.EtaleCohomology.EtaleSheaves.ChainsDiscCoprodPf
import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.ColimOf
import Development.EtaleCohomology.EtaleSheaves.CompPf
import Development.EtaleCohomology.EtaleSheaves.CompositionGoal
import Development.EtaleCohomology.EtaleSheaves.CoprodPf
import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.DescendPf
import Development.EtaleCohomology.EtaleSheaves.DomCoverPf
import Development.EtaleCohomology.EtaleSheaves.ArchimedeanCokernel
import Development.EtaleCohomology.EtaleSheaves.ArchimedeanComparison
import Development.EtaleCohomology.EtaleSheaves.KerLocOf
import Development.EtaleCohomology.EtaleSheaves.EtAffNbhdPf
import Development.EtaleCohomology.EtaleSheaves.EtAlgPf
import Development.EtaleCohomology.EtaleSheaves.EtStagePf
import Development.EtaleCohomology.EtaleSheaves.FiltPf
import Development.EtaleCohomology.EtaleSheaves.FracAICPf
import Development.EtaleCohomology.EtaleSheaves.FreeCoprodPf
import Development.EtaleCohomology.EtaleSheaves.GlobalPf
import Development.EtaleCohomology.EtaleSheaves.HKCoprodPf
import Development.EtaleCohomology.EtaleSheaves.HensIntPf
import Development.EtaleCohomology.EtaleSheaves.IECobPf
import Development.EtaleCohomology.EtaleSheaves.IdemCoverPf
import Development.EtaleCohomology.EtaleSheaves.IntClosPf
import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf
import Development.EtaleCohomology.EtaleSheaves.FiltrationLevelInjectivity
import Development.EtaleCohomology.EtaleSheaves.FiltrationLevelBase
import Development.EtaleCohomology.EtaleSheaves.LocAtPf
import Development.EtaleCohomology.EtaleSheaves.LocEtPf
import Development.EtaleCohomology.EtaleSheaves.LocIEPf
import Development.EtaleCohomology.EtaleSheaves.LocTensorPf
import Development.EtaleCohomology.EtaleSheaves.SimplicialPieceDiscrete
import Development.EtaleCohomology.EtaleSheaves.PointwisePf
import Development.EtaleCohomology.EtaleSheaves.PushGluePf
import Development.EtaleCohomology.EtaleSheaves.PushPf
import Development.EtaleCohomology.EtaleSheaves.RelDescPf
import Development.EtaleCohomology.EtaleSheaves.RelEqvInjPf
import Development.EtaleCohomology.EtaleSheaves.SHAlgSecPf
import Development.EtaleCohomology.EtaleSheaves.SHEqvPf
import Development.EtaleCohomology.EtaleSheaves.SHExistsPf
import Development.EtaleCohomology.EtaleSheaves.SHLocPf
import Development.EtaleCohomology.EtaleSheaves.SHSectionPf
import Development.EtaleCohomology.EtaleSheaves.SHTensorPf
import Development.EtaleCohomology.EtaleSheaves.SecPrePf
import Development.EtaleCohomology.EtaleSheaves.SepTensorPf
import Development.EtaleCohomology.EtaleSheaves.EtaleSpreading.SpreadOf
import Development.EtaleCohomology.EtaleSheaves.StalkCut
import Development.EtaleCohomology.EtaleSheaves.TowerFinPf
import Development.EtaleCohomology.EtaleSheaves.TruncationPieces
import Development.EtaleCohomology.EtaleSheaves.TruncBijPf
import Development.EtaleCohomology.EtaleSheaves.Truncation
import Development.EtaleCohomology.EtaleSheaves.TwFBijPf
import Development.EtaleCohomology.EtaleSheaves.SpSOfIntegralInjective
import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks.ULAStalkOf
import Development.EtaleCohomology.EtaleSheaves.ZariskiLocalCech
import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi
import Development.EtaleCohomology.WeilConjectures.AbsorbPf
import Development.EtaleCohomology.WeilConjectures.EtaleNeighborhoodsHaveCommonRefinement
import Development.EtaleCohomology.WeilConjectures.EtaleAlgebrasHaveSmallModelSet
import Development.EtaleCohomology.WeilConjectures.EtaleNeighborhoodsEqualizeParallelMaps

namespace UpperTheory.Et.E3

/- English proof (translation)
The claim follows from `@LateralTheory.E.CompPf.Comp_of`.
-/
theorem n2 : LateralTheory.E.AlgResPropsPf.Comp := @LateralTheory.E.CompPf.Comp_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.PushPf.Push_of`.
-/
theorem n3 : LateralTheory.E.AlgResPropsPf.Push := @LateralTheory.E.PushPf.Push_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.EtAlgPf.EtAlg_of`.
-/
theorem n4 : LateralTheory.E.AlgResPropsPf.EtAlg := @LateralTheory.E.EtAlgPf.EtAlg_of

/- English proof (translation)
Conclude with `LateralTheory.E.AlgResPropsPf.AlgResProps_of n2 n3 n4`.
-/
theorem n1 : LateralTheory.E.t_E3Cut.AlgResProps := by
  exact LateralTheory.E.AlgResPropsPf.AlgResProps_of n2 n3 n4

/- English proof (translation)
The claim follows from `@UpperTheory.cohomology_continuity_filtered_colimit_rings`.
-/
theorem n7 : LateralTheory.E.t_E3Cut.Limit := @UpperTheory.cohomology_continuity_filtered_colimit_rings

/- English proof (translation)
The claim follows from `@LateralTheory.E.t_E3Cut.etale_base_change_polynomial_induction_of_limit @n7`.
-/
theorem n6 : LateralTheory.E.t_E3Cut.EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := @LateralTheory.E.t_E3Cut.etale_base_change_polynomial_induction_of_limit @n7

/- English proof (translation)
The claim follows from `@LateralTheory.E.BasePf.Base_of @n6`.
-/
theorem n5 : LateralTheory.E.t_E3Cut.Base := @LateralTheory.E.BasePf.Base_of @n6

/- English proof (translation)
The claim follows from `@LateralTheory.E.SimplicialPieceDiscrete.Piece_of`.
-/
theorem n12 : LateralTheory.E.TruncationPieces.Piece := @LateralTheory.E.SimplicialPieceDiscrete.Piece_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.FiltPf.TowerFin_of`.
-/
theorem n15 : LateralTheory.E.FiltPf.TowerFin := @LateralTheory.E.FiltPf.TowerFin_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncPf.TruncBij_of`.
-/
theorem n17 : LateralTheory.E.TruncPf.TruncBij := @LateralTheory.E.TruncPf.TruncBij_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationInclusionIso.Trunc_of @n17`.
-/
theorem n16 : LateralTheory.E.FiltPf.Trunc := @LateralTheory.E.TruncationInclusionIso.Trunc_of @n17

/- English proof (translation)
The claim follows from `@LateralTheory.E.FiltPf.tower_of @n15 @n16`.
-/
theorem n14 : LateralTheory.E.FiltPf.Tower := @LateralTheory.E.FiltPf.tower_of @n15 @n16

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationPieces.Filt_of_tower @n14`.
-/
theorem n13 : LateralTheory.E.TruncationPieces.Filt := @LateralTheory.E.TruncationPieces.Filt_of_tower @n14

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationPieces.etale_relK_single_degree_pieces_of_piece_and_filtration @n12 @n13`.
-/
theorem n11 : LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels := @LateralTheory.E.TruncationPieces.etale_relK_single_degree_pieces_of_piece_and_filtration @n12 @n13

/- English proof (translation)
The claim follows from `@LateralTheory.E.CechSqPf.integral_surjective_ring_cech_augmentation_etale_eqv`.
-/
theorem n19 : LateralTheory.E.CechSqPf.IntegralSurjectiveRingCechAugmentationEtaleEqv := @LateralTheory.E.CechSqPf.integral_surjective_ring_cech_augmentation_etale_eqv

/- English proof (translation)
The claim follows from `@LateralTheory.E.CechSqPf.BaseChange_of`.
-/
theorem n20 : LateralTheory.E.CechSqPf.BaseChange := @LateralTheory.E.CechSqPf.BaseChange_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.CechSqPf.LevelPush_of`.
-/
theorem n21 : LateralTheory.E.CechSqPf.LevelPush := @LateralTheory.E.CechSqPf.LevelPush_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.CechSqPf.cechConerve_levelwise`.
-/
theorem n22 : LateralTheory.E.CechSqPf.LevelP := @LateralTheory.E.CechSqPf.cechConerve_levelwise

/- English proof (translation)
Conclude with `LateralTheory.E.CechSqPf.Level0_of n21`.
-/
theorem n23 : LateralTheory.E.CechSqPf.Level0 := by
  exact LateralTheory.E.CechSqPf.Level0_of n21

/- English proof (translation)
Conclude with `LateralTheory.E.CechSqPf.CechSq_of n19 n20 n21 n22 n23`.
-/
theorem n18 : LateralTheory.E.DescIntPf.CechSq := by
  exact LateralTheory.E.CechSqPf.CechSq_of n19 n20 n21 n22 n23

/- English proof (translation)
The claim follows from `@LateralTheory.E.DescIntPf.DescInt_of @n11 @n18`.
-/
theorem n10 : LateralTheory.E.StalkCut.DescInt := @LateralTheory.E.DescIntPf.DescInt_of @n11 @n18

/- English proof (translation)
The claim follows from `@LateralTheory.E.FreeCoprodPf.FreeCoprod_of`.
-/
theorem n27 : LateralTheory.E.CoprodPf.FreeCoprod := @LateralTheory.E.FreeCoprodPf.FreeCoprod_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.ChainsDiscCoprodPf.ChainsDiscCoprod_of`.
-/
theorem n28 : LateralTheory.E.CoprodPf.ChainsDiscCoprod := @LateralTheory.E.ChainsDiscCoprodPf.ChainsDiscCoprod_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.HKCoprodPf.HKCoprod_of`.
-/
theorem n29 : LateralTheory.E.CoprodPf.HKCoprod := @LateralTheory.E.HKCoprodPf.HKCoprod_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.CoprodPf.Coprod_of @n27 @n28 @n29`.
-/
theorem n26 : LateralTheory.E.t_E3Cut.Coprod := @LateralTheory.E.CoprodPf.Coprod_of @n27 @n28 @n29

/- English proof (translation)
The claim follows from `@LateralTheory.E.PointwisePf.pushColim`.
-/
theorem n31 : LateralTheory.E.PointwisePf.PushColim := @LateralTheory.E.PointwisePf.pushColim

/- English proof (translation)
Conclude with `LateralTheory.E.PointwisePf.Pointwise_of_pushColim n31`.
-/
theorem n30 : LateralTheory.E.KillCokPf.Pointwise := by
  exact LateralTheory.E.PointwisePf.Pointwise_of_pushColim n31

/- English proof (translation)
The claim follows from `@LateralTheory.E.PushGluePf.PushGlue_of @n26`.
-/
theorem n32 : LateralTheory.E.KillCokPf.Glue.PushGlue := @LateralTheory.E.PushGluePf.PushGlue_of @n26

/- English proof (translation)
The claim follows from `@LateralTheory.E.KillCokPf.Glue.KillCok_of' @n26 @n30 @n32`.
-/
theorem n25 : LateralTheory.E.DescLocPf.Fine.KillCok := @LateralTheory.E.KillCokPf.Glue.KillCok_of' @n26 @n30 @n32

/- English proof (translation)
The claim follows from `@LateralTheory.E.RelEqvInjPf.RelEqvInj_of`.
-/
theorem n35 : LateralTheory.E.RelDescPf.RelEqvInj := @LateralTheory.E.RelEqvInjPf.RelEqvInj_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.RelDescPf.cechEqv`.
-/
theorem n36 : LateralTheory.E.RelDescPf.CechEqv := @LateralTheory.E.RelDescPf.cechEqv

/- English proof (translation)
The claim follows from `@UpperTheory.Cb.simplicial_chains_degree_zero_injective @n26`.
-/
theorem n39 : LateralTheory.E.FiltrationLevelBase.Step0 := @UpperTheory.Cb.simplicial_chains_degree_zero_injective @n26

/- English proof (translation)
The claim follows from `@LateralTheory.E.FiltrationLevelBase.Filt_of @n39`.
-/
theorem n38 : LateralTheory.E.FiltrationLevelInjectivity.Filt := @LateralTheory.E.FiltrationLevelBase.Filt_of @n39

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of`.
-/
theorem n40 : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := @LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of @n38 @n40`.
-/
theorem n37 : LateralTheory.E.RelDescPf.LevelInj := @LateralTheory.E.FiltrationLevelInjectivity.LevelInj_of @n38 @n40

/- English proof (translation)
The claim follows from `@LateralTheory.E.RelDescPf.relDesc_of @n35 @n36 @n37`.
-/
theorem n34 : LateralTheory.E.TruncationKernel.RelDesc := @LateralTheory.E.RelDescPf.relDesc_of @n35 @n36 @n37

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of @n34`.
-/
theorem n33 : LateralTheory.E.DescLocPf.Fine.TruncCok := @LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of @n34

/- English proof (translation)
The claim follows from `@LateralTheory.E.KernelLocalization.KerLoc_of @n26 @n34`.
-/
theorem n41 : LateralTheory.E.DescLocPf.KerLoc := @LateralTheory.E.KernelLocalization.KerLoc_of @n26 @n34

/- English proof (translation)
The claim follows from `@LateralTheory.E.DescLocPf.Fine.DescLoc_of' @n25 @n33 @n41`.
-/
theorem n24 : LateralTheory.E.StalkCut.DescLoc := @LateralTheory.E.DescLocPf.Fine.DescLoc_of' @n25 @n33 @n41

/- English proof (translation)
The claim follows from `@LateralTheory.E.StalkCut.goal_of @n10 @n24`.
-/
theorem n9 : LateralTheory.E.t_E3Cut.Stalk := @LateralTheory.E.StalkCut.goal_of @n10 @n24

/- English proof (translation)
The claim follows from `@LateralTheory.EWeil.AbsorbPf3.etaleAlgebras_have_small_model_set`.
-/
theorem n47 : LateralTheory.EWeil.AbsorbPf.Model := @LateralTheory.EWeil.AbsorbPf3.etaleAlgebras_have_small_model_set

/- English proof (translation)
The claim follows from `@LateralTheory.EWeil.AbsorbPf2.etaleNeighborhoods_have_common_refinement`.
-/
theorem n48 : LateralTheory.EWeil.AbsorbPf.Pair := @LateralTheory.EWeil.AbsorbPf2.etaleNeighborhoods_have_common_refinement

/- English proof (translation)
The claim follows from `@LateralTheory.EWeil.AbsorbPf4.etaleNeighborhoods_equalize_parallel_maps`.
-/
theorem n49 : LateralTheory.EWeil.AbsorbPf.Coeq := @LateralTheory.EWeil.AbsorbPf4.etaleNeighborhoods_equalize_parallel_maps

/- English proof (translation)
The claim follows from `@LateralTheory.EWeil.AbsorbPf.Absorb_of @n47 @n48 @n49`.
-/
theorem n46 : LateralTheory.E.ColimPf.Absorb := @LateralTheory.EWeil.AbsorbPf.Absorb_of @n47 @n48 @n49

/- English proof (translation)
The claim follows from `@LateralTheory.E.EtStagePf.EtStage_of`.
-/
theorem n52 : LateralTheory.E.SpreadPf.Cut.EtStage := @LateralTheory.E.EtStagePf.EtStage_of

/- English proof (translation)
Conclude with `LateralTheory.E.SpreadPf.Main.Spread_of n52`.
-/
theorem n51 : LateralTheory.E.DescendPf.Spread := by
  exact LateralTheory.E.SpreadPf.Main.Spread_of n52

/- English proof (translation)
The claim follows from `@LateralTheory.E.DescendPf.Descend_of @n51`.
-/
theorem n50 : LateralTheory.E.ColimPf.Descend := @LateralTheory.E.DescendPf.Descend_of @n51

/- English proof (translation)
The claim follows from `@LateralTheory.E.ColimPf.Main.Colim_of @n46 @n50`.
-/
theorem n45 : LateralTheory.E.SHLocPf.Colim := @LateralTheory.E.ColimPf.Main.Colim_of @n46 @n50

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHLocPf.build_of @n45`.
-/
theorem n44 : LateralTheory.E.SHLocPf.Build := @LateralTheory.E.SHLocPf.build_of @n45

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHLocPf.etaleClosed_point_lifts_simple_roots_monic`.
-/
theorem n53 : LateralTheory.E.SHLocPf.Lift := @LateralTheory.E.SHLocPf.etaleClosed_point_lifts_simple_roots_monic

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHLocPf.SHLoc_of @n44 @n53`.
-/
theorem n43 : LateralTheory.E.SHExistsPf.SHLoc := @LateralTheory.E.SHLocPf.SHLoc_of @n44 @n53

/- English proof (translation)
The claim follows from `@LateralTheory.E.LocAtPf.LocAt_of`.
-/
theorem n54 : LateralTheory.E.SHExistsPf.LocAt := @LateralTheory.E.LocAtPf.LocAt_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.CompositionGoal.goal_of`.
-/
theorem n55 : LateralTheory.E.SHExistsPf.Comp := @LateralTheory.E.CompositionGoal.goal_of

/- English proof (translation)
Conclude with `LateralTheory.E.SHExistsPf.SHExists_of n43 n54 n55`.
-/
theorem n42 : LateralTheory.E.t_E3Cut.SHExists := by
  exact LateralTheory.E.SHExistsPf.SHExists_of n43 n54 n55

/- English proof (translation)
The claim follows from `@LateralTheory.E.TruncationIsoComparison.IEComp_of`.
-/
theorem n56 : LateralTheory.E.t_E3Cut.IEComp := @LateralTheory.E.TruncationIsoComparison.IEComp_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHAlgSecPf.SHAlgSec_of`.
-/
theorem n59 : LateralTheory.E.SHSectionPf.SHAlgSec := @LateralTheory.E.SHAlgSecPf.SHAlgSec_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.EtAffNbhdPf.EtAffNbhd_of`.
-/
theorem n60 : LateralTheory.E.SHSectionPf.EtAffNbhd := @LateralTheory.E.EtAffNbhdPf.EtAffNbhd_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHSectionPf.SHSection_of @n59 @n60`.
-/
theorem n58 : LateralTheory.E.t_E3Cut.SHSection := @LateralTheory.E.SHSectionPf.SHSection_of @n59 @n60

/- English proof (translation)
The claim follows from `@LateralTheory.E.SecPrePf.SecPre_of @n58`.
-/
theorem n62 : LateralTheory.E.SHEqvPf.SecPre := @LateralTheory.E.SecPrePf.SecPre_of @n58

/- English proof (translation)
The claim follows from `@LateralTheory.E.TwFBijPf.TwFBij_of`.
-/
theorem n63 : LateralTheory.E.SHEqvPf.TwFBij := @LateralTheory.E.TwFBijPf.TwFBij_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHEqvPf.SecBij_of @n62 @n63`.
-/
theorem n61 : LateralTheory.E.SHEqvPf.SecBij := @LateralTheory.E.SHEqvPf.SecBij_of @n62 @n63

/- English proof (translation)
The claim follows from `@LateralTheory.E.SHEqvPf.SHEqv_of_secBij @n58 @n61`.
-/
theorem n57 : LateralTheory.E.t_E3Cut.SHEqv := @LateralTheory.E.SHEqvPf.SHEqv_of_secBij @n58 @n61

/- English proof (translation)
The claim follows from `@LateralTheory.E.AICExtPf.AICExt_of`.
-/
theorem n65 : LateralTheory.E.t_E3Cut.AICExt := @LateralTheory.E.AICExtPf.AICExt_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.IdemCoverPf.IdemCover_of`.
-/
theorem n67 : LateralTheory.E.DomCoverPf.IdemCover := @LateralTheory.E.IdemCoverPf.IdemCover_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.DomCoverPf.DomCover_of @n67`.
-/
theorem n66 : LateralTheory.E.t_E3Cut.DomCover := @LateralTheory.E.DomCoverPf.DomCover_of @n67

/- English proof (translation)
The claim follows from `@LateralTheory.E.LocIEPf.LocIE_of`.
-/
theorem n68 : LateralTheory.E.t_E3Cut.LocIE := @LateralTheory.E.LocIEPf.LocIE_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.HensIntPf.HensInt_of`.
-/
theorem n71 : LateralTheory.E.t_E3Cut.HensInt := @LateralTheory.E.HensIntPf.HensInt_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.IntClosPf.IntClos_of @n71`.
-/
theorem n70 : LateralTheory.E.t_E3Cut.IntClos := @LateralTheory.E.IntClosPf.IntClos_of @n71

/- English proof (translation)
The claim follows from `@LateralTheory.E.LocTensorPf.LocTensor_of`.
-/
theorem n73 : LateralTheory.E.SHTensorPf.LocTensor := @LateralTheory.E.LocTensorPf.LocTensor_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.SepTensorPf.SepTensor_of`.
-/
theorem n74 : LateralTheory.E.SHTensorPf.SepTensor := @LateralTheory.E.SepTensorPf.SepTensor_of

/- English proof (translation)
Conclude with `LateralTheory.E.SHTensorPf.SHTensor_of n71 n73 n74`.
-/
theorem n72 : LateralTheory.E.t_E3Cut.SHTensor := by
  exact LateralTheory.E.SHTensorPf.SHTensor_of n71 n73 n74

/- English proof (translation)
The claim follows from `@LateralTheory.E.t_E3Cut.AICSH_of`.
-/
theorem n75 : LateralTheory.E.t_E3Cut.AICSH := @LateralTheory.E.t_E3Cut.AICSH_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.IECobPf.IECob_of`.
-/
theorem n76 : LateralTheory.E.ULAStalkPf.IECob := @LateralTheory.E.IECobPf.IECob_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.FracAICPf.FracAIC_of`.
-/
theorem n77 : LateralTheory.E.ULAStalkPf.FracAIC := @LateralTheory.E.FracAICPf.FracAIC_of

/- English proof (translation)
Conclude with `LateralTheory.E.ULAStalkPf.ULAStalk_of' n70 n72 n75 n57 n6 n76 n77`.
-/
theorem n69 : LateralTheory.E.t_E3Cut.ULAStalk := by
  exact LateralTheory.E.ULAStalkPf.ULAStalk_of' n70 n72 n75 n57 n6 n76 n77

/- English proof (translation)
The claim follows from `@LateralTheory.E.ULAPf.ULA_of @n9 @n1 @n65 @n66 @n68 @n69`.
-/
theorem n64 : LateralTheory.E.t_E3Cut.ULA := @LateralTheory.E.ULAPf.ULA_of @n9 @n1 @n65 @n66 @n68 @n69

/- English proof (translation)
Conclude with `UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation n9 n7 n42 n56 n1 n57 n64`.
-/
theorem n8 : LateralTheory.E.t_E3Cut.Step := by
  exact UpperTheory.Cb.strictHenselization_stalk_equiv_of_colimit_presentation n9 n7 n42 n56 n1 n57 n64

/- English proof (translation)
The claim follows from `@LateralTheory.E.CechSigma_xy1Pf_Yo.cechYoneda`.
-/
theorem n81 : LateralTheory.E.CechSigma_xy1Pf_Lev.CechYoneda := @LateralTheory.E.CechSigma_xy1Pf_Yo.cechYoneda

/- English proof (translation)
The claim follows from `@UpperTheory.Cb.cechLevel_iso_sigma_intersections_of_coprod @n26`.
-/
theorem n82 : LateralTheory.E.CechSigma_xy1Pf_Lev.SchemeLevel := @UpperTheory.Cb.cechLevel_iso_sigma_intersections_of_coprod @n26

/- English proof (translation)
Conclude with `LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of n81 n82`.
-/
theorem n80 : LateralTheory.E.ZariskiLocalCech.CechSigma := by
  exact LateralTheory.E.CechSigma_xy1Pf_Lev.CechSigma_of n81 n82

/- English proof (translation)
The claim follows from `@LateralTheory.E.ZariskiLocalCech.ZarLocal_of @n26 @n80`.
-/
theorem n79 : LateralTheory.E.t_E3Cut.ZarLocal := @LateralTheory.E.ZariskiLocalCech.ZarLocal_of @n26 @n80

/- English proof (translation)
The claim follows from `@LateralTheory.E.AffinePf.Affine_of`.
-/
theorem n83 : LateralTheory.E.GlobalPf.Affine := @LateralTheory.E.AffinePf.Affine_of

/- English proof (translation)
The claim follows from `@LateralTheory.E.LocEtPf.LocEt_of`.
-/
theorem n84 : LateralTheory.E.GlobalPf.LocEt := @LateralTheory.E.LocEtPf.LocEt_of

/- English proof (translation)
Conclude with `LateralTheory.E.GlobalPf.Global_of n79 n83 n84`.
-/
theorem n78 : LateralTheory.E.t_E3Cut.Global := by
  exact LateralTheory.E.GlobalPf.Global_of n79 n83 n84

open CategoryTheory LateralTheory.E.t_E3Cut in

/- English proof (translation)
Introduce `q _ T _ _ _ hAIC hq X p _ i`. Establish `hAR : LateralTheory.E.t_E3Cut.AlgRes (CommRingCat.ofHom (algebraMap T (FractionRing T)))`. Introduce `Q hQ c`. Take `⟨⟨a, b⟩, hc⟩` from `IsLocalization.surj (nonZeroDivisors T) c`. Establish `hb : algebraMap T (FractionRing T) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2`.

Use `⟨Polynomial.C (b : T) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `hmem`. Apply `hQ.ne_top` to reduce the goal to its premises. Apply `Ideal.eq_top_of_isUnit_mem _ _ (IsUnit.mk0 _ hb)` to reduce the goal to its premises. Simplify using `using hmem`.

Establish `h0 : Polynomial.eval₂ (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap T (FractionRing T)))) c (Polynomial.C (b : T) * Polynomial.X - Polynomial.C a) = 0`. Simplify using `only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X]`. Rewrite using `[mul_comm, hc, sub_self]`. Rewrite using `[h0]`. Conclude with `Q.zero_mem`.

Establish `hgood : ∀ n : ℕ, LateralTheory.E.t_E3Cut.Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T))) (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `LateralTheory.E.t_E3Cut.Good.of_equiv (n5 H q i T hAIC hq) (MvPolynomial.isEmptyAlgEquiv T (Fin 0)).symm.toRingEquiv _ ?_` and prove the remaining obligations.

Use extensionality with `x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Use `LateralTheory.E.t_E3Cut.Good.of_equiv (n8 H q i _ _ hq hAR ih) (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_` and prove the remaining obligations. Apply `CommRingCat.hom_ext` to reduce the goal to its premises.

Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`. Express the relevant statement in the definitionally equal form `(MvPolynomial.finSuccEquiv T n).symm (algebraMap T _ x) = algebraMap T (MvPolynomial (Fin (n + 1)) T) x`. Conclude with `AlgEquiv.commutes _ x`. Conclude with `n78 H q i _ hgood p`.
-/
theorem main (H : LateralTheory.E.t_E3Cut.Hyp) : GlobalTheory.EtC.E3 := by
  intro q _ T _ _ _ hAIC hq X p _ i
  have hAR : LateralTheory.E.t_E3Cut.AlgRes (CommRingCat.ofHom (algebraMap T (FractionRing T))) := by
    intro Q hQ c
    obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors T) c
    have hb : algebraMap T (FractionRing T) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
    refine ⟨Polynomial.C (b : T) * Polynomial.X - Polynomial.C a, ⟨1, ?_⟩, ?_⟩
    · intro hmem
      apply hQ.ne_top
      apply Ideal.eq_top_of_isUnit_mem _ _ (IsUnit.mk0 _ hb)
      simpa using hmem
    · have h0 : Polynomial.eval₂ (CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap T (FractionRing T)))) c
          (Polynomial.C (b : T) * Polynomial.X - Polynomial.C a) = 0 := by
        simp only [CommRingCat.hom_ofHom, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        rw [mul_comm, hc, sub_self]
      rw [h0]
      exact Q.zero_mem
  have hgood : ∀ n : ℕ, LateralTheory.E.t_E3Cut.Good q i (CommRingCat.ofHom (algebraMap T (FractionRing T)))
      (CommRingCat.ofHom (MvPolynomial.C : T →+* MvPolynomial (Fin n) T)) := by
    intro n
    induction n with
    | zero =>
      refine LateralTheory.E.t_E3Cut.Good.of_equiv (n5 H q i T hAIC hq)
        (MvPolynomial.isEmptyAlgEquiv T (Fin 0)).symm.toRingEquiv _ ?_
      ext x
      simp
    | succ n ih =>
      refine LateralTheory.E.t_E3Cut.Good.of_equiv (n8 H q i _ _ hq hAR ih)
        (MvPolynomial.finSuccEquiv T n).symm.toRingEquiv _ ?_
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change (MvPolynomial.finSuccEquiv T n).symm (algebraMap T _ x) = algebraMap T (MvPolynomial (Fin (n + 1)) T) x
      exact AlgEquiv.commutes _ x
  exact n78 H q i _ hgood p

end UpperTheory.Et.E3
