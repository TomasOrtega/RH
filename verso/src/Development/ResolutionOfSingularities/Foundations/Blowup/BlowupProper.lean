import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupCartier
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.Blowup

/- English proof (authored)
On an affine scheme, an ideal sheaf is determined by its global section ideal. The sheaf built from the given global ideal has that same global ideal, so it equals the original sheaf.
-/
private theorem ofIdealTop_ideal_top_eq_self {X : Scheme.{u}} [IsAffine X] (I : X.IdealSheafData) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
      (I.ideal ⟨⊤, isAffineOpen_top X⟩) = I :=
  Scheme.IdealSheafData.ext_of_isAffine (by simp)

/- English proof (authored)
Extending an ideal along the isomorphism and then its inverse equals extending it along the identity. Identity extension fixes the ideal.
-/
private theorem map_inv_map_hom_eq_self {A B : CommRingCat.{u}} (e : A ≅ B) (K : Ideal ↑A) :
    Ideal.map (CommRingCat.Hom.hom e.inv) (Ideal.map (CommRingCat.Hom.hom e.hom) K) = K := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, e.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]

/- English proof (authored)
Transport the given ideal of global sections to the original ring by the affine spectrum isomorphism. The associated ideal sheaf is the given sheaf by the affine correspondence. The affine Rees blowup of this ring ideal has the required blowup property and is proper because the ring is Noetherian.
-/
private theorem exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I : (Spec (CommRingCat.of A)).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec (CommRingCat.of A)),
      IsBlowupAlongIdealSheaf π I ∧ AlgebraicGeometry.IsProper π := by
  obtain ⟨J, hJ⟩ : ∃ J : Ideal A, FunctorialResolution.Blowup.specIdealSheaf J = I := by
    refine ⟨Ideal.map (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
      (I.ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩), ?_⟩
    rw [FunctorialResolution.Blowup.specIdealSheaf_eq_ofIdealTop, map_inv_map_hom_eq_self (Scheme.ΓSpecIso (CommRingCat.of A))]
    exact ofIdealTop_ideal_top_eq_self I
  refine ⟨FunctorialResolution.Blowup.affineBlowup J, FunctorialResolution.Blowup.AffineBlowup.toSpec J, ?_,
    FunctorialResolution.Blowup.isProper_affineBlowup_toSpec J⟩
  rw [← hJ]
  exact FunctorialResolution.Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec J

/- English proof (authored)
Apply the affine existence and properness result to the commutative ring represented by the given spectrum.
-/
theorem exists_isBlowupAlongIdealSheaf_isProper_spec (R : CommRingCat.{u}) [IsNoetherianRing ↑R]
    (I : (Spec R).IdealSheafData) :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Spec R), IsBlowupAlongIdealSheaf π I ∧ AlgebraicGeometry.IsProper π :=
  exists_isBlowupAlongIdealSheaf_isProper_spec_of_isNoetherianRing (↑R) I

/- English proof (authored)
Identify the base with the spectrum of its global section ring and transport the center along that isomorphism. There is a proper affine blowup for the transported center. The universal properties of it and the given blowup give mutually inverse maps over the spectrum, so the given projection is a composite of the proper affine blowup with isomorphisms. It is therefore proper.
-/
theorem isProper_of_isBlowupAlongIdealSheaf_of_isAffine {Y B : Scheme.{u}} [IsAffine Y]
    [IsNoetherianRing Γ(Y, ⊤)] (J : Y.IdealSheafData) {p : B ⟶ Y} (h : IsBlowupAlongIdealSheaf p J) :
    AlgebraicGeometry.IsProper p := by
  obtain ⟨Y', π, hπ, hproper⟩ :=
    exists_isBlowupAlongIdealSheaf_isProper_spec Γ(Y, ⊤) (J.comap Y.isoSpec.inv)
  have hq : IsBlowupAlongIdealSheaf (p ≫ Y.isoSpec.hom) (J.comap Y.isoSpec.inv) := h.comp_iso_hom Y.isoSpec
  obtain ⟨b, hb⟩ := hπ.exists_lift (p ≫ Y.isoSpec.hom) hq.1
  obtain ⟨a, ha⟩ := hq.exists_lift π hπ.1
  have hab : a ≫ b = 𝟙 Y' := by
    refine hπ.hom_ext hπ.1 ?_ ?_
    · rw [Category.assoc, hb, ha]
    · rw [Category.id_comp]
  have hba : b ≫ a = 𝟙 B := by
    refine hq.hom_ext hq.1 ?_ ?_
    · rw [Category.assoc, ha, hb]
    · rw [Category.id_comp]
  have : IsIso b := ⟨a, hba, hab⟩
  have : AlgebraicGeometry.IsProper π := hproper
  have hp : b ≫ π ≫ Y.isoSpec.inv = p := by
    rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← hp]
  infer_instance

/- English proof (authored)
The pullback scheme along the open inclusion is canonically isomorphic to the inverse-image open. Under this isomorphism its second projection is the restriction of the original map. Properness is invariant under an isomorphism of the source and hence transfers.
-/
private theorem isProper_morphismRestrict_of_isProper_pullbackSnd {X X' : Scheme.{u}} (f : X' ⟶ X)
    (U : X.Opens) (h : AlgebraicGeometry.IsProper (pullback.snd f U.ι)) :
    AlgebraicGeometry.IsProper (AlgebraicGeometry.morphismRestrict f U) := by
  have key : (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
      AlgebraicGeometry.morphismRestrict f U = pullback.snd f U.ι := by
    simp [AlgebraicGeometry.morphismRestrict]
  have h2 : AlgebraicGeometry.IsProper
      ((AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom ≫
        AlgebraicGeometry.morphismRestrict f U) := by
    rw [key]; exact h
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.IsProper)
    (AlgebraicGeometry.pullbackRestrictIsoRestrict f U).hom
    (AlgebraicGeometry.morphismRestrict f U)).mp h2

/- English proof (authored)
Sections on the affine open are Noetherian because the ambient scheme is locally Noetherian. They identify with global sections of that open as a scheme, and Noetherianity is preserved by ring isomorphism.
-/
private theorem isNoetherianRing_sections_top_of_affineOpen {X : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (U : X.affineOpens) :
    IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := by
  have : IsNoetherianRing Γ(X, (U : X.Opens)) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian U
  exact isNoetherianRing_of_ringEquiv _
    (CategoryTheory.Iso.commRingCatIsoToRingEquiv ((U : X.Opens).topIso)).symm

/- English proof (authored)
Cover the locally Noetherian base by its affine opens. Each affine open has a Noetherian global section ring. The pullback over it is a blowup of the restricted center, so it is proper by the affine result. Identifying these pullbacks with restrictions gives properness on the target cover. Properness is local on the target, proving the assertion.
-/
theorem blowupIsProper : BlowupIsProper.{u} := by
  intro X X' hX π Z hZ
  have := hX
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.IsProper)
    (fun U : X.affineOpens => (U : X.Opens)) (AlgebraicGeometry.iSup_affineOpens_eq_top X) ?_
  intro U
  have : AlgebraicGeometry.IsAffine (U : X.Opens).toScheme := U.2
  have : IsNoetherianRing Γ((U : X.Opens).toScheme, ⊤) := isNoetherianRing_sections_top_of_affineOpen U
  exact isProper_morphismRestrict_of_isProper_pullbackSnd π (U : X.Opens)
    (isProper_of_isBlowupAlongIdealSheaf_of_isAffine (Z.comap (U : X.Opens).ι)
      (hZ.pullback_snd_of_isOpenImmersion (U : X.Opens).ι))

/- English proof (authored)
The properness theorem for blowups over locally Noetherian schemes applies to the given projection and ideal.
-/
theorem isProper_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.IsProper π :=
  blowupIsProper X X' π I h

/- English proof (authored)
The blowup projection is proper over the locally Noetherian base. Properness implies that it is locally of finite type.
-/
theorem locallyOfFiniteType_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.LocallyOfFiniteType π := by
  have := isProper_of_isBlowupAlongIdealSheaf h
  infer_instance

/- English proof (authored)
The blowup projection is proper by the locally Noetherian result, and proper morphisms are quasi-compact.
-/
theorem quasiCompact_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {π : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsBlowupAlongIdealSheaf π I) : AlgebraicGeometry.QuasiCompact π := by
  have := isProper_of_isBlowupAlongIdealSheaf h
  infer_instance

end FunctorialResolution.Blowup
