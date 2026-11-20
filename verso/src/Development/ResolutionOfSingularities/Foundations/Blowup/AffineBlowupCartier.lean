import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowup
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.ReesGrading
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace FunctorialResolution.Blowup

universe u

variable {R : Type u} [CommRing R]

def specIdealSheaf (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)

/- English proof (authored)
Identify the original ring with the global sections of its spectrum. The ideal sheaf is defined by transporting the original ideal to that section ring and applying the affine ideal-sheaf correspondence.
-/
theorem specIdealSheaf_eq_ofIdealTop (I : Ideal R) :
    specIdealSheaf I =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I) := rfl

/- English proof (authored)
The affine correspondence recovers an ideal from the global sections of its associated ideal sheaf. Here the corresponding ideal is the original ideal transported to the section ring of its spectrum.
-/
theorem specIdealSheaf_ideal_top (I : Ideal R) :
    (specIdealSheaf I).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I :=
  Scheme.IdealSheafData.ofIdealTop_ideal_top _

def chartSectionsIso (I : Ideal R) (a : ↥I) :
    CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) ≅
      Γ(affineBlowup I, affineBlowupChart I a ''ᵁ ⊤) :=
  (Scheme.ΓSpecIso
      (CommRingCat.of (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).symm ≪≫
    ((affineBlowupChart I a).appIso ⊤).symm

/- English proof (authored)
The chart ring is first identified with the global sections of its spectrum. The inverse of the open-immersion isomorphism on sections then identifies these with the sections on the chart image.
-/
theorem chartSectionsIso_hom (I : Ideal R) (a : ↥I) :
    (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso
          (CommRingCat.of
            (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv ≫
        ((affineBlowupChart I a).appIso ⊤).inv := rfl

/- English proof (authored)
Apply the defining composite to the chosen element, first using the affine spectrum identification and then the inverse of the open-immersion section isomorphism.
-/
theorem chartSectionsIso_hom_apply (I : Ideal R) (a : ↥I)
    (x : HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)) :
    (chartSectionsIso I a).hom.hom x =
      ((affineBlowupChart I a).appIso ⊤).inv.hom
        ((Scheme.ΓSpecIso
            (CommRingCat.of
              (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a)))).inv.hom x) := rfl

/- English proof (authored)
Identify the open with the whole scheme and then identify the two section maps. The restriction to the whole scheme is the identity, so the composite gives the given map.
-/
private theorem comp_presheaf_map_eq_of_heq {Z : Scheme.{u}} {A : CommRingCat.{u}} (U : Z.Opens) (hU : U = ⊤)
    (φ : A ⟶ Γ(Z, U)) (h : (⊤ : Z.Opens) ≤ U) (ψ : A ⟶ Γ(Z, (⊤ : Z.Opens)))
    (hφ : HEq φ ψ) : φ ≫ Z.presheaf.map (homOfLE h).op = ψ := by
  subst hU
  obtain rfl : φ = ψ := eq_of_heq hφ
  rw [show (homOfLE h : (⊤ : Z.Opens) ⟶ ⊤) = 𝟙 (⊤ : Z.Opens) from rfl]
  simp

/- English proof (authored)
The inverse image of the whole target is the whole source. The restriction in the specified section map is therefore the identity, giving the global section map.
-/
private theorem appTop_eq_appLE_top_top {Z S : Scheme.{u}} (f : Z ⟶ S)
    (h : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens)) : f.appLE ⊤ ⊤ h = f.appTop :=
  comp_presheaf_map_eq_of_heq (f ⁻¹ᵁ (⊤ : S.Opens)) (le_antisymm le_top h) (f.app ⊤) h f.appTop HEq.rfl

/- English proof (authored)
The open-immersion section isomorphism is the section map from the image open to the whole immersed scheme. Compose it with the restriction of the other map and use functoriality of section maps. The resulting composite is between global sections and is the stated global section map.
-/
private theorem appLE_image_top_comp_appIso_hom {Z X S : Scheme.{u}} (g : Z ⟶ X)
    [IsOpenImmersion g] (p : X ⟶ S)
    (e : (g ''ᵁ (⊤ : Z.Opens)) ≤ p ⁻¹ᵁ (⊤ : S.Opens)) :
    p.appLE ⊤ (g ''ᵁ ⊤) e ≫ (g.appIso ⊤).hom = (g ≫ p).appTop := by
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  exact appTop_eq_appLE_top_top (g ≫ p) _

/- English proof (authored)
The blowup projection restricted to the chart is the spectrum map induced by the chart ring homomorphism. On global sections this agrees with the original ring homomorphism under the spectrum section isomorphisms. Transport the chart's sections to the image open to get the restricted map in the claim.
-/
theorem chartRingHom_comp_chartSectionsIso_hom (I : Ideal R) (a : ↥I) :
    CommRingCat.ofHom (chartRingHom I a) ≫ (chartSectionsIso I a).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
          (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm) := by
  rw [chartSectionsIso_hom, ← Category.assoc, Iso.comp_inv_eq, Category.assoc,
    appLE_image_top_comp_appIso_hom, affineBlowupChart_comp_toSpec, algebraMap_chart_eq_chartRingHom]
  exact Scheme.ΓSpecIso_inv_naturality _

/- English proof (authored)
On the affine chart image, the pullback section ideal is extension of the original ideal along the restricted section map. The chart section identity factors this ring map through the chart ring. On the chart ring the extended ideal is generated by the image of the chart generator. Transporting along the chart section isomorphism carries this generator to the stated section.
-/
theorem ideal_comap_toSpec_chart_eq_span (I : Ideal R) (a : ↥I)
    (hW : IsAffineOpen (affineBlowupChart I a ''ᵁ ⊤)) :
    ((specIdealSheaf I).comap (AffineBlowup.toSpec I)).ideal ⟨_, hW⟩ =
      Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
  have hcomp := congrArg CommRingCat.Hom.hom (chartRingHom_comp_chartSectionsIso_hom I a)
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hcomp
  have key : Ideal.map ((AffineBlowup.toSpec I).appLE ⊤ (affineBlowupChart I a ''ᵁ ⊤)
        (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)).hom
        (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I)
      = Ideal.span {(chartSectionsIso I a).hom.hom (chartRingHom I a (a : R))} := by
    rw [Ideal.map_map, ← hcomp, ← Ideal.map_map, map_chartRingHom_eq_span_singleton, Ideal.map_span,
      Set.image_singleton]
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE (specIdealSheaf I) (AffineBlowup.toSpec I)
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of R))⟩ ⟨_, hW⟩
      (le_top.trans_eq (Scheme.Hom.preimage_top (AffineBlowup.toSpec I)).symm)]
  rw [specIdealSheaf_ideal_top]
  exact key

/- English proof (authored)
Every blowup point lies on an affine chart. There the pulled-back ideal is generated by the chart generator transported to the section ring of the chart image. This generator is a nonzerodivisor in the chart ring, and the section-ring isomorphism preserves that property.
-/
theorem isLocallyGeneratedByNonZeroDivisor_comap_toSpec (I : Ideal R) :
    IsLocallyGeneratedByNonZeroDivisor ((specIdealSheaf I).comap (AffineBlowup.toSpec I)) := by
  intro x
  obtain ⟨a, hx⟩ : ∃ a : ↥I, x ∈ Set.range (affineBlowupChart I a).base :=
    ⟨(affineBlowupAffineOpenCover I).idx x, (affineBlowupAffineOpenCover I).covers x⟩
  have hW := (isAffineOpen_top (Spec (CommRingCat.of
      (HomogeneousLocalization.Away (reesGrading I) (reesGenerator I a))))).image_of_isOpenImmersion
      (affineBlowupChart I a)
  refine ⟨⟨_, hW⟩, (chartSectionsIso I a).hom.hom (chartRingHom I a (a : R)), ?_, ?_,
    ideal_comap_toSpec_chart_eq_span I a hW⟩
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, trivial, hy⟩
  · exact map_mem_nonZeroDivisors_of_iso (chartSectionsIso I a) (chartRingHom_mem_nonZeroDivisors I a)

end FunctorialResolution.Blowup
