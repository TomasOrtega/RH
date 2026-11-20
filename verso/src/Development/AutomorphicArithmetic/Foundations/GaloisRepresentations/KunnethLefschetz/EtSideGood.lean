import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DiagonalEtaleThreeOfFirst
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AffineProperBaseChange

namespace UpperTheory.Gal.KunnethLefschetz
open GlobalTheory.EtC CrystallineSemistableComparison

structure Core : Prop where
  c2 : C2
  c3 : C3
  c4 : C4
  c5 : C5
  d1 : D1

namespace Core
variable (H : Core)
include H

/- English proof (translation)
The claim follows from `h GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExac …`.
-/
theorem upTo {P : Prop} (h : A1 → A2 → A3 → A4 → A5 → A7 → A8 → A9 → A10 → A11 → B1 → B2 → B3 → B4 → B5 → B7 → C1 → C2 → C3 → C4 →
    C5 → D1 → P) : P :=
  h GlobalTheory.T.quasiIso_hypercohomology_bijective GlobalTheory.T.etC_a2 GlobalTheory.T.levelwiseEquivalence_isEquivalence GlobalTheory.T.mayerVietoris_equivalence_of_cover GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero
    GlobalTheory.T.etaleCohomology_bijective_of_support_bijective RedCoef.a11 GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity UpperTheory.etaleCohomology_functorialityAxioms_hold GlobalTheory.T.etC_b3 UpperTheory.etaleCohomology_excisionAxiom_holds GlobalTheory.T.absolutelyIntegrallyClosed_domain_tateTwistAcyclic GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology
    GlobalTheory.EtC.gaugeSplitting_holds H.c2 H.c3 H.c4 H.c5 H.d1

/- English proof (translation)
The claim follows from `H.upTo (LateralTheory.E.D2.goal_of (LateralTheory.E.D2.LeafRing_of GlobalTheory.T.cup_chern_kummer_pullback_naturality GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold) LateralTheory.E.D2.LeafChern_of (LateralTheory.E.D2.LeafNat_of GlobalTheory.T.cup_chern_kummer_pullback_natu …`.
-/
theorem d2 : D2 := H.upTo (LateralTheory.E.D2.goal_of (LateralTheory.E.D2.LeafRing_of GlobalTheory.T.cup_chern_kummer_pullback_naturality GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold) LateralTheory.E.D2.LeafChern_of
  (LateralTheory.E.D2.LeafNat_of GlobalTheory.T.cup_chern_kummer_pullback_naturality)
  (LateralTheory.E.D2.LeafWhitney_of (LateralTheory.E.LeafGeomPfLoc.LeafGeom_of LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
    (LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of LateralTheory.E.LeafMapWPf.LeafMapW_of)) LateralTheory.E.LeafCover2Pf.LeafCover2_of GlobalTheory.T.cup_vanishes_on_two_member_cover GlobalTheory.T.cup_chern_kummer_pullback_naturality)
  (LateralTheory.E.D2.LeafLine_of GlobalTheory.T.cup_chern_kummer_pullback_naturality) LateralTheory.E.LeafNewtonPf.LeafNewton_of)

/- English proof (translation)
The claim follows from `H.upTo UpperTheory.Et.D3.intersectionNumber_baseChange H.d2`.
-/
theorem d3 : D3 := H.upTo UpperTheory.Et.D3.intersectionNumber_baseChange H.d2

/- English proof (translation)
The claim follows from `UpperTheory.Et.E3.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCoho …`.
-/
theorem e3 : E3 :=
  UpperTheory.Et.E3.main ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity,
    UpperTheory.etaleCohomology_functorialityAxioms_hold, UpperTheory.etaleCohomology_excisionAxiom_holds, H.c3, H.c4⟩

/- English proof (translation)
The claim follows from `H.upTo UpperTheory.Et.e4 H.d2 H.d3 UpperTheory.Et.affine_proper_base_change (duality_diagonalClass_of_affineProperBaseChange UpperTheory.Et.affine_proper_base_change) H.e3`.
-/
theorem e4 : E4 := H.upTo UpperTheory.Et.e4 H.d2 H.d3 UpperTheory.Et.affine_proper_base_change (duality_diagonalClass_of_affineProperBaseChange UpperTheory.Et.affine_proper_base_change) H.e3

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.cup_chern_kummer_pullback_natura …`.
-/
theorem inputs : In :=
  ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.positiveDegreeClasses_die_on_etaleCover, GlobalTheory.T.cup_chern_kummer_pullback_naturality, GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold, GlobalTheory.T.cup_vanishes_on_two_member_cover,
    GlobalTheory.T.chernClass_kummerClass_additive, GlobalTheory.T.etaleCohomology_coefficient_longExactSequence, GlobalTheory.T.etaleCohomology_coefficientRing_invariance, GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, GlobalTheory.T.etaleCohomology_bijective_of_support_bijective, RedCoef.a11, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, UpperTheory.etaleCohomology_functorialityAxioms_hold,
    GlobalTheory.T.etC_b3, H.c4, H.d1, duality_diagonalClass_of_affineProperBaseChange UpperTheory.Et.affine_proper_base_change, H.e3, H.e4,
    UpperTheory.Et.purGysin ⟨GlobalTheory.T.quasiIso_hypercohomology_bijective, GlobalTheory.T.etC_a2, GlobalTheory.T.levelwiseEquivalence_isEquivalence, GlobalTheory.T.mayerVietoris_equivalence_of_cover, GlobalTheory.T.cup_chern_kummer_pullback_naturality, GlobalTheory.T.cupProduct_gradedCommRingAxioms_hold,
      GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero, RedCoef.a11, GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity, H.c4, H.d1, UpperTheory.Et.affine_proper_base_change⟩, LateralTheory.KummerTheory.goal_holds⟩

/- English proof (translation)
The claim follows from `qDual_holds H.inputs trIn_holds`.
-/
theorem qDual : QDual := qDual_holds H.inputs trIn_holds

/- English proof (translation)
The claim follows from `qDiag_holds H.inputs trIn_holds`.
-/
theorem qDiag : QDiag := qDiag_holds H.inputs trIn_holds

/- English proof (translation)
The claim follows from `Di.diagEt3_of H.inputs H.qDiag`.
-/
theorem diagEt3 : CrystallineSemistableComparison.Onto.DiagEt3 := Di.diagEt3_of H.inputs H.qDiag

/- English proof (translation)
The claim follows from `KunnethLefschetz.etSide_sm H.inputs H.qDual inSum_holds CrystallineSemistableComparison.comp CrystallineSemistableComparison.geo l K`.
-/
theorem etSide_sm (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    EtSide (Model.Sm (l := l) (K := K)) := KunnethLefschetz.etSide_sm H.inputs H.qDual inSum_holds CrystallineSemistableComparison.comp CrystallineSemistableComparison.geo l K

/- English proof (translation)
The claim follows from `etFin_of H.inputs H.qDual inSum_holds CrystallineSemistableComparison.comp CrystallineSemistableComparison.geo`.
-/
theorem etFin : CrystallineSemistableComparison.Onto.EtFin := etFin_of H.inputs H.qDual inSum_holds CrystallineSemistableComparison.comp CrystallineSemistableComparison.geo

end Core

end UpperTheory.Gal.KunnethLefschetz
