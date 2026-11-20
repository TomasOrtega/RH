import Development.EtaleCohomology.EtaleSheaves.TwPairExists
import Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle
import Development.EtaleCohomology.EtaleSheaves.GoalOf
import Development.EtaleCohomology.EtaleSheaves.LeafSupport
import Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
import Development.EtaleCohomology.EtaleSheaves.LeafChernPf
import Development.EtaleCohomology.EtaleSheaves.LeafCochainVanishPf
import Development.EtaleCohomology.EtaleSheaves.LeafCover2Of
import Development.EtaleCohomology.EtaleSheaves.LeafExtTensPf
import Development.EtaleCohomology.EtaleSheaves.LeafGeomPfLoc
import Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
import Development.EtaleCohomology.EtaleSheaves.HalfDegreeVanishing.SecondBlockUnimodularLocusInclusionMono
import Development.EtaleCohomology.EtaleSheaves.BaerFlatZModCriterion
import Development.EtaleCohomology.EtaleSheaves.LeafInjSecInjOf
import Development.EtaleCohomology.EtaleSheaves.LeafLinePf
import Development.EtaleCohomology.EtaleSheaves.LeafMapWPf
import Development.EtaleCohomology.EtaleSheaves.LeafNatPf
import Development.EtaleCohomology.EtaleSheaves.LeafNewtonPf
import Development.EtaleCohomology.EtaleSheaves.UnitExistence.CocycleOfSec
import Development.EtaleCohomology.EtaleSheaves.LeafOneLocPf
import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf
import Development.EtaleCohomology.EtaleSheaves.LeafPairExtPf
import Development.EtaleCohomology.EtaleSheaves.PairExtensionOfTensorUniversal
import Development.EtaleCohomology.EtaleSheaves.LeafPreTensLocInjPf
import Development.EtaleCohomology.EtaleSheaves.LeafPrimCoverPf
import Development.EtaleCohomology.EtaleSheaves.PrimitiveRootLocalization
import Development.EtaleCohomology.EtaleSheaves.LeafRepVanishPf
import Development.EtaleCohomology.EtaleSheaves.RingCommutativity
import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf
import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
import Development.EtaleCohomology.EtaleSheaves.LeafSecInjPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensFactorPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensMonoPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoGenPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensQIsoPf
import Development.EtaleCohomology.EtaleSheaves.LeafTensUPPf
import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocGenOf
import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocSplitOf
import Development.EtaleCohomology.EtaleSheaves.LeafTw0GenFreeOf
import Development.EtaleCohomology.EtaleSheaves.LeafTw0TwFreeOf
import Development.EtaleCohomology.EtaleSheaves.LeafTwPairHtpyPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwPairUniquePf
import Development.EtaleCohomology.EtaleSheaves.LeafTwResHtpyPf
import Development.EtaleCohomology.EtaleSheaves.LeafTwTensExistsPf
import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
import Development.EtaleCohomology.EtaleSheaves.LeafUnitAWPf
import Development.EtaleCohomology.EtaleSheaves.LeafUnitActPf
import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairGPf
import Development.EtaleCohomology.EtaleSheaves.LeafUnitPairPf
import Development.EtaleCohomology.EtaleSheaves.UnitSections
import Development.EtaleCohomology.EtaleSheaves.LeafWhitneyPf
import Development.EtaleCohomology.EtaleSheaves.LeafZModInjFlatPf
import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.Fix.EtaleChapterDTwo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem awSpec : LateralTheory.E.LeafA6suppPf.LeafAWSpec := by
  intro q _ E n m i j α β
  have hS := LateralTheory.Fix.CupProductTensor.cupSpec (ZMod q) (twPair q i j) E (rfl : n + m = n + m)
  obtain ⟨γ, hγ⟩ := hS.1 α β
  exact ⟨γ, hγ, hS.2 α β γ hγ⟩

/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FEtaleFirstChernClassRepresentedByChernCocycle.lean&line=43#L43)
-/
theorem s0 : LateralTheory.E.D2.LeafA6nat := @_root_.LateralTheory.E.LeafA6nat_xy7V2Cut.goal_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FTwPairExists.lean&line=85#L85)
-/
theorem s1 : LateralTheory.E.CupProductRingLaws.LeafCupSpec := @_root_.LateralTheory.Fix.CupProductTensor.cupSpec
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FTwPairExists.lean&line=99#L99)
-/
theorem s2 : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := @_root_.LateralTheory.Fix.CupProductTensor.twPairExists
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTwTensExistsPf.lean&line=177#L177)
-/
theorem s3 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTensFactorPf.lean&line=131#L131)
-/
theorem s4 : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s5 : LateralTheory.E.ZModFlatnessFromBaerCriterion.TensTwRes := @_root_.GlobalTheory.EtC.isTwRes_tensor
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafInjSecInjOf.lean&line=38#L38)
-/
theorem s6 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s7 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s8 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of s5 s6 s7
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTwResHtpyPf.lean&line=46#L46)
-/
theorem s9 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s10 : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := @_root_.LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of s3 s4 s8 s9
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FWeightBoundsExistence.lean&line=218#L218)
-/
theorem s11 : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := @_root_.LateralTheory.E.FreeSheafGeneratorLifts.LeafHtpyAW_proved
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s12 : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := @_root_.LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of s1 s10 s11
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FUnitSections.lean&line=25#L25)
-/
theorem s13 : LateralTheory.E.LeafOneExistsPf.LeafUnitSec := @_root_.LateralTheory.E.UnitSections.LeafUnitSec_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s14 : LateralTheory.E.LeafOneSpecPf.LeafOneExists := @_root_.LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit s13
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafPrimCoverPf.lean&line=64#L64)
-/
theorem s15 : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := @_root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s16 : LateralTheory.E.CupProductRingLaws.LeafOneSpec := @_root_.LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of s14 s15
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s17 : LateralTheory.E.LeafUnitActPf.LeafActSheaf := @_root_.LateralTheory.E.LeafActSheafPf.LeafActSheaf_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s18 : LateralTheory.E.LeafUnitPairGPf.LeafUnitAct := @_root_.LateralTheory.E.LeafUnitActPf.LeafUnitAct_of s17
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTensUPPf.lean&line=68#L68)
-/
theorem s19 : LateralTheory.E.LeafPairExtPf2.LeafTensUP := @_root_.LateralTheory.E.LeafTensUPPf.etale_tensor_pairing_universal_property_holds
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTw0LocGenOf.lean&line=50#L50)
-/
theorem s20 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := @_root_.LateralTheory.E.LeafTw0LocGenPf.LeafTw0LocGen_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTw0TwFreeOf.lean&line=26#L26)
-/
theorem s21 : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := @_root_.LateralTheory.E.LeafTw0TwFreePf.LeafTw0TwFree_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s22 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := @_root_.LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0GenFree_of s21
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s23 : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := @_root_.LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of s20 s22
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s24 : LateralTheory.E.LeafTensMonoPf.LeafPreTensLocInj := @_root_.LateralTheory.E.LeafPreTensLocInjPf.LeafPreTensLocInj_of s23
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s25 : LateralTheory.E.LeafExtTensPf.LeafTensMono := @_root_.LateralTheory.E.LeafTensMonoPf.LeafTensMono_of s24
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafTensQIsoGenPf.lean&line=24#L24)
-/
theorem s26 : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := @_root_.LateralTheory.E.LeafTensQIsoGenPf.LeafTensQIsoGen_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafSecInjPf.lean&line=34#L34)
-/
theorem s27 : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := @_root_.LateralTheory.E.LeafSecInjPf.LeafSecInj_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafZModInjFlatPf.lean&line=99#L99)
-/
theorem s28 : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := @_root_.LateralTheory.E.LeafZModInjFlatPf.LeafZModInjFlat_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s29 : LateralTheory.E.LeafExtTensPf.LeafTensQIso := @_root_.LateralTheory.E.LeafTensQIsoPf.LeafTensQIso_of s26 s27 s28
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s30 : LateralTheory.E.LeafPairExtPf2.LeafExtTens := @_root_.LateralTheory.E.LeafExtTensPf.LeafExtTens_of s25 s29
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s31 : LateralTheory.E.LeafPairExtPf.LeafExtAlongAug := @_root_.LateralTheory.E.LeafPairExtPf2.LeafExtAlongAug_of s19 s30
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s32 : LateralTheory.E.LeafUnitPairGPf.LeafPairExt := @_root_.LateralTheory.E.LeafPairExtPf.LeafPairExt_of' s31
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s33 : LateralTheory.E.LeafUnitPairPf.LeafUnitPairG := @_root_.LateralTheory.E.LeafUnitPairGPf.LeafUnitPairG_of s18 s32
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s34 : LateralTheory.E.LeafRingUnitPf.LeafUnitPair := @_root_.LateralTheory.E.LeafUnitPairPf.LeafUnitPair_of s33
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FPrimitiveRootLocalization.lean&line=70#L70)
-/
theorem s35 : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := @_root_.LateralTheory.E.PrimitiveRootLocalization.LeafPrimLoc_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s36 : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := @_root_.LateralTheory.E.LeafOneLocPf.LeafOneLoc_of s35
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s37 : LateralTheory.E.LeafRingUnitPf.LeafUnitAW := @_root_.LateralTheory.E.LeafUnitAWPf.LeafUnitAW_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s38 : LateralTheory.E.CupProductRingLaws.LeafRingUnit := @_root_.LateralTheory.E.LeafRingUnitPf.LeafRingUnit_of s1 s2 s12 s16 s34 s36 s37
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FTwPairExists.lean&line=84#L84)
-/
theorem s39 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := @_root_.LateralTheory.Fix.CupProductTensor.ringAssoc
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FRingCommutativity.lean&line=5#L5)
-/
theorem s40 : LateralTheory.E.CupProductRingLaws.LeafRingComm := @_root_.LateralTheory.E.RingCommutativity.goal_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s41 : LateralTheory.E.D2.LeafA6ring := @_root_.LateralTheory.E.LeafA6ringCut.goal_of s38 s39 s40
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s42 : LateralTheory.E.D2.LeafRing := @_root_.LateralTheory.E.D2.LeafRing_of s0 s41
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s43 : LateralTheory.E.D2.LeafChern := @_root_.LateralTheory.E.D2.LeafChern_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s44 : LateralTheory.E.D2.LeafNat := @_root_.LateralTheory.E.D2.LeafNat_of s0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s45 : LateralTheory.E.LeafGeomPf.LeafHalf1 := @_root_.LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafMapWPf.lean&line=95#L95)
-/
theorem s46 : LateralTheory.E.HalfDegreeVanishing.LeafMapW := @_root_.LateralTheory.E.LeafMapWPf.LeafMapW_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s47 : LateralTheory.E.LeafGeomPf.LeafHalf2 := @_root_.LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of s46
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s48 : LateralTheory.E.D2.LeafGeom := @_root_.LateralTheory.E.LeafGeomPfLoc.LeafGeom_of s45 s47
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafCover2Of.lean&line=56#L56)
-/
theorem s49 : LateralTheory.E.D2.LeafCover2 := @_root_.LateralTheory.E.LeafCover2Pf.LeafCover2_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s50 : LateralTheory.E.LeafA6suppPf.LeafAWSpec := awSpec
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafRepVanishPf.lean&line=57#L57)
-/
theorem s51 : LateralTheory.E.LeafA6suppPf.LeafRepVanish := @_root_.LateralTheory.E.LeafRepVanishPf.LeafRepVanish_of
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafCochainVanishPf.lean&line=57#L57)
-/
theorem s52 : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := @_root_.LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s53 : LateralTheory.E.D2.LeafA6supp := @_root_.LateralTheory.E.LeafA6suppPf.LeafA6supp_of s50 s51 s52
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s54 : LateralTheory.E.D2.LeafWhitney := @_root_.LateralTheory.E.D2.LeafWhitney_of s48 s49 s53 s0
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s55 : LateralTheory.E.D2.LeafLine := @_root_.LateralTheory.E.D2.LeafLine_of s0
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FEtaleCohomology%2FEtaleSheaves%2FLeafNewtonPf.lean&line=77#L77)
-/
theorem s56 : LateralTheory.E.D2.LeafNewton := @_root_.LateralTheory.E.LeafNewtonPf.LeafNewton_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem s57 : LateralTheory.E.EtaleChapterDTwo := @_root_.LateralTheory.E.D2.goal_of s42 s43 s44 s54 s55 s56

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.E.EtaleChapterDTwo := s57

end LateralTheory.Fix.EtaleChapterDTwo
