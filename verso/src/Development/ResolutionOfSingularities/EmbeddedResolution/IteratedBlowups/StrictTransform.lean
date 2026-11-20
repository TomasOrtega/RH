import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((D.comap π).subscheme).Opens :=
  (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl

/- English proof (authored)
The open in the pulled-back closed subscheme consists exactly of the points whose images lie outside the support of the pulled-back center ideal. This is the inverse image defining the open.
-/
theorem coe_strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((strictTransformOpens π Z D : ((D.comap π).subscheme).Opens) :
        Set ((D.comap π).subscheme)) =
      ⇑(D.comap π).subschemeι.base ⁻¹' ((Z.comap π).support.compl : Set X₁) := rfl

def strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (strictTransformOpens π Z D).toScheme ⟶ X₁ :=
  Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι

/- English proof (authored)
The strict-transform immersion first includes the open away from the exceptional support into the pulled-back subscheme and then includes that closed subscheme into the ambient scheme.
-/
theorem strictTransformι_eq_ι_comp_subschemeι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransformι π Z D =
      Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι := rfl

/- English proof (authored)
Both constructions are the same composite of the open inclusion away from the pulled-back center and the closed immersion of the pulled-back subscheme.
-/
theorem strictTransformImmersion_eq_strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransformImmersion π Z D = strictTransformι π Z D := rfl

/- English proof (authored)
The strict-transform ideal is the ideal of the scheme-theoretic image of the open immersion into the pulled-back subscheme followed by its ambient inclusion. This is the kernel ideal sheaf of the displayed immersion.
-/
theorem strictTransform_eq_ker_strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D = (strictTransformι π Z D).ker := rfl

/- English proof (authored)
For a quasi-compact morphism, the kernel ideal on an affine target open is the kernel of the homomorphism from its section ring to the sections over its inverse image.
-/
private theorem ker_ideal_eq_ker_app {W Z : Scheme.{u}} (g : W ⟶ Z) [QuasiCompact g]
    (U : Z.affineOpens) :
    (Scheme.Hom.ker g).ideal U = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
  simp

/- English proof (authored)
A point belongs to the range of the composite exactly when it is the image under the second map of some value of the first map. This gives equality with the image of the first range.
-/
private theorem range_comp_eq_image_range {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    Set.range ⇑(f ≫ g) = ⇑g '' Set.range ⇑f := by
  ext x
  simp [Set.range_comp]

/- English proof (authored)
Precomposing with an isomorphism changes the induced maps on sections by isomorphisms on their targets. These preserve exactly which sections map to zero, so the kernel ideal sheaf is unchanged.
-/
theorem ker_eq_ker_of_isIso_comp {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    [IsIso e] (h : e ≫ g = f) : f.ker = g.ker := by
  subst h; exact Scheme.Hom.ker_comp_of_isIso e g

/- English proof (authored)
The image of the inverse image lies inside the original open. Conversely, any point of that open belongs to the larger open by hypothesis and so has a lift to the larger open whose image is the point itself.
-/
private theorem image_preimage_ι_of_le {X : Scheme.{u}} (U O : X.Opens) (h : O ≤ U) :
    Scheme.Opens.ι U ''ᵁ (Scheme.Opens.ι U ⁻¹ᵁ O) = O := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact hy
  · intro x hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩

/- English proof (authored)
Take an affine open in the restricted target and identify it with its image in the ambient target. Its inverse images under the restricted map and the original map likewise identify via the open inclusion of the restricted source. The corresponding square of section maps commutes. The horizontal identifications of the section rings are isomorphisms, so an ambient section lies in the original kernel exactly when its restricted section lies in the new kernel. The affine charts therefore give equality of the two ideal sheaves.
-/
theorem ker_comap_ι_eq_ker_morphismRestrict {W T : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker (m ∣_ V) := by
  refine Scheme.IdealSheafData.ext ?_
  funext P
  have hQaff : IsAffineOpen (Scheme.Opens.ι V ''ᵁ P.1) :=
    P.2.image_of_isOpenImmersion (Scheme.Opens.ι V)
  have hpre : Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) = P.1 :=
    (Scheme.Opens.ι V).preimage_image_eq P.1
  have e : P.1 ≤ Scheme.Opens.ι V ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := hpre.ge
  have hpre2 : ((m ∣_ V) ⁻¹ᵁ P.1)
      = Scheme.Opens.ι (m ⁻¹ᵁ V) ⁻¹ᵁ (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) := by
    rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage, hpre]
  have hQV : (Scheme.Opens.ι V ''ᵁ P.1) ≤ V := Scheme.Opens.ι_image_le V P.1
  have hle : m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) ≤ m ⁻¹ᵁ V := fun x hx => hQV hx
  have himg : Scheme.Opens.ι (m ⁻¹ᵁ V) ''ᵁ ((m ∣_ V) ⁻¹ᵁ P.1)
      = m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1) := by
    rw [hpre2]
    exact image_preimage_ι_of_le (m ⁻¹ᵁ V) (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) hle
  have hbij := IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι V)
    (Scheme.Opens.ι V ''ᵁ P.1) P.1 e rfl
  have hinj := (IsOpenImmersion.bijective_appLE_of_image_eq (Scheme.Opens.ι (m ⁻¹ᵁ V))
    (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le himg).1
  have hsq : Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e ≫
        (m ∣_ V).app P.1
      = m.app (Scheme.Opens.ι V ''ᵁ P.1) ≫
        Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le := by
    rw [Scheme.Hom.app_eq_appLE (m ∣_ V), Scheme.Hom.app_eq_appLE m,
      Scheme.Hom.appLE_comp_appLE (m ∣_ V) (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1
        ((m ∣_ V) ⁻¹ᵁ P.1) e le_rfl,
      Scheme.Hom.appLE_comp_appLE (Scheme.Opens.ι (m ⁻¹ᵁ V)) m (Scheme.Opens.ι V ''ᵁ P.1)
        (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) le_rfl hpre2.le]
    exact Scheme.Hom.appLE_congr_hom (morphismRestrict_ι m V) ..
  have hsqr : ∀ x, (CommRingCat.Hom.hom ((m ∣_ V).app P.1))
        ((CommRingCat.Hom.hom
          (Scheme.Hom.appLE (Scheme.Opens.ι V) (Scheme.Opens.ι V ''ᵁ P.1) P.1 e)) x)
      = (CommRingCat.Hom.hom (Scheme.Hom.appLE (Scheme.Opens.ι (m ⁻¹ᵁ V))
          (m ⁻¹ᵁ (Scheme.Opens.ι V ''ᵁ P.1)) ((m ∣_ V) ⁻¹ᵁ P.1) hpre2.le))
        ((CommRingCat.Hom.hom (m.app (Scheme.Opens.ι V ''ᵁ P.1))) x) := by
    intro x
    have h' := congrArg (fun mm => (CommRingCat.Hom.hom mm) x) hsq
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h'
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ (Scheme.Opens.ι V)
      ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩ P e,
    ker_ideal_eq_ker_app m ⟨Scheme.Opens.ι V ''ᵁ P.1, hQaff⟩, ker_ideal_eq_ker_app (m ∣_ V) P]
  dsimp only
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hsqr x]
    rw [RingHom.mem_ker] at hx
    rw [hx, map_zero]
  · intro y hy
    rw [RingHom.mem_ker] at hy
    obtain ⟨x, rfl⟩ := hbij.2 y
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker]
    apply hinj
    rw [← hsqr x, hy, map_zero]

/- English proof (authored)
Restriction along the open inclusion gives the kernel of the restricted morphism. The new morphism is obtained from it by precomposition with an isomorphism, which preserves the kernel.
-/
theorem ker_comap_ι_eq_ker_of_isIso_comp {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by
  rw [ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]

/- English proof (authored)
The support of the kernel ideal of the quasi-compact immersion is the closure of its point image. That image is the support of the pulled-back subscheme ideal intersected with the complement of the pulled-back center support. Both pulled-back supports are inverse images. Taking their difference commutes with inverse image, giving the asserted closure.
-/
theorem support_strictTransform_eq_closure_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (⇑π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
  have h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) =
      (⇑π.base ⁻¹' (Z.support : Set X))ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]
  congr 1
  rw [strictTransformι_eq_ι_comp_subschemeι, range_comp_eq_image_range, Scheme.Opens.range_ι,
    coe_strictTransformOpens, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, h1, h2]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  tauto

/- English proof (authored)
Replace each pulled-back support by the inverse image of its original support. The difference of the two inverse images is the inverse image of the difference, so the previous closure description gives the equality.
-/
theorem support_strictTransform_eq_closure_sdiff {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (((D.comap π).support : Set X₁) \ ((Z.comap π).support : Set X₁)) := by
  have h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]

/- English proof (authored)
The pulled-back subscheme ideal is the kernel of its closed immersion. The strict-transform immersion is obtained by precomposing that immersion with an open inclusion. Every section vanishing on the whole subscheme still vanishes on its open part, yielding the containment.
-/
theorem comap_le_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    D.comap π ≤ Blowup.strictTransform π Z D := by
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  calc D.comap π = (D.comap π).subschemeι.ker :=
        (Scheme.IdealSheafData.ker_subschemeι _).symm
    _ ≤ _ := Scheme.Hom.le_ker_comp _ _

/- English proof (authored)
Pullback of the unit ideal is the unit ideal. The total-transform ideal is contained in the strict-transform ideal, so the latter contains the unit ideal and equals it.
-/
theorem strictTransform_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z (⊤ : X.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [Scheme.IdealSheafData.comap_top] at h
  exact le_antisymm le_top h

/- English proof (authored)
Pulling back the kernel of the composite along the open immersion recovers the kernel of the closed immersion. The latter is the ideal defining that closed subscheme.
-/
theorem comap_ker_subschemeι_comp {A B : Scheme.{u}} (K : A.IdealSheafData) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.subschemeι] [QuasiCompact (K.subschemeι ≫ f)] :
    (K.subschemeι ≫ f).ker.comap f = K := by
  rw [Blowup.comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]

/- English proof (authored)
Restricting the closed immersion to the open gives the base change of the closed immersion by the open inclusion. The pullback closed immersion is defined by the pulled-back ideal, so this ideal is its kernel.
-/
private theorem ker_morphismRestrict_subschemeι {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (K.subschemeι ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso]

/- English proof (authored)
The restriction of the given closed immersion and the closed immersion defined by the pulled-back ideal have the same kernel. The equal kernels give a factorization of the first immersion through the second and make the resulting morphism an isomorphism. Its factorization equation is the asserted compatibility.
-/
private theorem exists_isIso_subschemeι_preimage_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    ∃ e : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ (K.comap (Scheme.Opens.ι V)).subscheme,
      IsIso e ∧ e ≫ (K.comap (Scheme.Opens.ι V)).subschemeι = K.subschemeι ∣_ V := by
  have hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι
      (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V)
    (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk

/- English proof (authored)
The restriction of the closed immersion factors through an isomorphism to the closed subscheme of the restricted ideal. The equation for restricting a morphism identifies the two ambient maps after that isomorphism. Precomposition with the isomorphism leaves the kernel unchanged.
-/
theorem ker_ι_preimage_comp_subschemeι_eq_ker_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (Scheme.Opens.ι (K.subschemeι ⁻¹ᵁ V) ≫ K.subschemeι).ker =
      ((K.comap (Scheme.Opens.ι V)).subschemeι ≫ Scheme.Opens.ι V).ker := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_subschemeι_preimage_comap K V
  have := he
  rw [← morphismRestrict_ι K.subschemeι V, ← hfac, Category.assoc]
  exact Scheme.Hom.ker_comp_of_isIso e _

/- English proof (authored)
The blowup is an isomorphism over the complement of the center. Under this isomorphism the open used in the strict transform identifies with the restriction of the original closed subscheme to that complement. It is therefore reduced because the original subscheme is reduced. The kernel ideal of a morphism from a reduced scheme is radical, so the scheme-theoretic closure defining the strict transform is reduced.
-/
theorem isReduced_subscheme_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) [IsReduced D.subscheme]
    [QuasiCompact (strictTransformι π Z D)] :
    IsReduced (Blowup.strictTransform π Z D).subscheme := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨e₁, he₁, -⟩ := exists_isIso_subschemeι_preimage_comap (D.comap π) (π ⁻¹ᵁ Z.support.compl)
  obtain ⟨e₂, he₂, -⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl)
      (D.comap (Scheme.Opens.ι Z.support.compl))
  obtain ⟨e₃, he₃, -⟩ := exists_isIso_subschemeι_preimage_comap D Z.support.compl
  have := he₁
  have := he₂
  have := he₃
  have : IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))
  have : IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion (inv e₃)
  have : IsReduced
      ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion e₂
  have : IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme := by
    rw [hcc]; infer_instance
  have : IsReduced (strictTransformOpens π Z D).toScheme := by
    have hrw : strictTransformOpens π Z D
        = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl) := by
      show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
          = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e₁
  rw [strictTransform_eq_ker_strictTransformι]
  exact isReduced_subscheme_ker _

/- English proof (authored)
The complement of the pulled-back center support is the inverse image of the center complement. Restrict the total-transform subscheme to this open. Its ideal is the pullback of the original ideal restricted to the center complement, by the commuting restriction square. The strict-transform kernel is consequently the kernel of this restricted closed immersion followed by the ambient open inclusion.
-/
theorem strictTransform_eq_ker_restrict {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by
  have hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl))
      = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫
      (D₁.comap f).subschemeι).ker = _
  rw [hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]

/- English proof (authored)
The restricted kernel formula computes the strict transform using only the ideal restricted to the complement of the center. The two restrictions agree by hypothesis, hence so do the two strict transforms.
-/
theorem strictTransform_congr_of_comap_ι_eq {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by
  rw [strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]

/- English proof (authored)
The pullback of the center ideal along the new morphism is the pullback of the original Cartier ideal along the given isomorphism and thus is Cartier. For any morphism satisfying the blowup lifting condition, take its unique lift to the original blowup and compose with the inverse isomorphism. This gives a lift to the new source. Any other lift would compose with the forward isomorphism to give the original lift, proving uniqueness.
-/
theorem isBlowupAlongIdealSheaf_of_isIso_comp {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : X.IdealSheafData) (hg : Blowup.IsBlowupAlongIdealSheaf g I) :
    Blowup.IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hcart.comap_of_isOpenImmersion e
  · intro Y q hq
    obtain ⟨t, ht, huniq⟩ := huniv Y q hq
    have ht' : t ≫ g = q := ht
    refine ⟨t ≫ inv e, ?_, ?_⟩
    · show (t ≫ inv e) ≫ f = q
      rw [← hfac, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht'
    · intro y hy
      have hy' : y ≫ f = q := hy
      have hye : y ≫ e = t := by
        refine huniq _ ?_
        show (y ≫ e) ≫ g = q
        rw [Category.assoc, hfac]
        exact hy'
      rw [← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/- English proof (authored)
Regard the given subset as a subset of the Noetherian subspace. Every subset of a Noetherian space is quasi-compact. Its image under the continuous inclusion is the original subset, hence is quasi-compact in the ambient space.
-/
private theorem isCompact_of_subset_noetherianSpace {α : Type u} [TopologicalSpace α] (s : Set α)
    [NoetherianSpace s] (t : Set α) (ht : t ⊆ s) : IsCompact t := by
  have h1 : IsCompact ((Subtype.val : s → α) ⁻¹' t) := NoetherianSpace.isCompact _
  have h2 := h1.image continuous_subtype_val
  have h3 : (Subtype.val : s → α) '' ((Subtype.val : s → α) ⁻¹' t) = t := by
    apply Set.Subset.antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hy
    · intro x hx
      exact ⟨⟨x, ht hx⟩, hx, rfl⟩
  rwa [h3] at h2

/- English proof (authored)
Cover the larger quasi-compact set by finitely many affine opens. Each of those opens is Noetherian because the scheme is locally Noetherian, so its intersection with the smaller set is quasi-compact. The smaller set is the finite union of those intersections and is quasi-compact.
-/
private theorem isCompact_of_subset_isCompact {B : Scheme.{u}} [IsLocallyNoetherian B]
    {U : Set B} (hc : IsCompact U) {T : Set B} (hT : T ⊆ U) : IsCompact T := by
  have hcov : U ⊆ ⋃ W : B.affineOpens, (W.1 : Set B) := by
    intro x _
    have hx : x ∈ (⊤ : B.Opens) := Set.mem_univ x
    rw [← iSup_affineOpens_eq_top B] at hx
    obtain ⟨W, hW⟩ := Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨W, hW⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : B.affineOpens => (W.1 : Set B)) (fun W => W.1.isOpen) hcov
  have hTeq : T = ⋃ W ∈ (s : Set B.affineOpens), (T ∩ (W.1 : Set B)) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨W, hWs, hxW⟩ := Set.mem_iUnion₂.mp (hs (hT hx))
      exact Set.mem_biUnion (show W ∈ (s : Set B.affineOpens) from hWs) ⟨hx, hxW⟩
    · intro x hx
      obtain ⟨W, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1
  rw [hTeq]
  refine (Finset.finite_toSet s).isCompact_biUnion ?_
  intro W _
  have : IsNoetherianRing (B.presheaf.obj (Opposite.op (W.1 : B.Opens))) :=
    IsLocallyNoetherian.component_noetherian W
  have : NoetherianSpace (W.1 : Set B) := noetherianSpace_of_isAffineOpen W.1 W.2
  exact isCompact_of_subset_noetherianSpace (W.1 : Set B) (T ∩ (W.1 : Set B)) Set.inter_subset_right

/- English proof (authored)
The image of the inverse image of a quasi-compact open is a subset of that open. In a locally Noetherian scheme it is therefore quasi-compact. An inducing map reflects quasi-compactness from the image to the inverse-image space, proving quasi-compactness of the morphism.
-/
private theorem quasiCompact_of_isInducing {A B : Scheme.{u}} [IsLocallyNoetherian B]
    (f : A ⟶ B) (hf : Topology.IsInducing ⇑f.base) : QuasiCompact f := by
  refine ⟨fun U _ hU' => ?_⟩
  refine hf.isCompact_iff.mpr ?_
  exact isCompact_of_subset_isCompact hU' (Set.image_preimage_subset _ _)

/- English proof (authored)
The strict-transform immersion is a composite of an open immersion and a closed immersion. Both induce the subspace topology and so does their composite. Since the ambient target is locally Noetherian, the quasi-compactness criterion for an inducing morphism applies.
-/
theorem quasiCompact_strictTransformι_of_isLocallyNoetherian {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) := by
  refine quasiCompact_of_isInducing _ ?_
  have h1 : Topology.IsInducing ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base :=
    (Scheme.Opens.ι (strictTransformOpens π Z D)).isEmbedding.toIsInducing
  have h2 : Topology.IsInducing ⇑(D.comap π).subschemeι.base :=
    (D.comap π).subschemeι.isEmbedding.toIsInducing
  have heq : ⇑(strictTransformι π Z D).base
      = ⇑(D.comap π).subschemeι.base ∘
        ⇑(Scheme.Opens.ι (strictTransformOpens π Z D)).base := rfl
  rw [heq]
  exact h2.comp h1

instance instQuasiCompactStrictTransformMorphism {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) :=
  quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D

end FunctorialResolution.EmbeddedResolution
