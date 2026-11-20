import Mathlib

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FunctorialResolution.EmbeddedResolution

namespace SmoothEtaleChart

/- English proof (authored)
Reindex the polynomial variables by the canonical bijection from the lifted index set to the original index set. This gives a polynomial-ring isomorphism that fixes the constants. Precomposing g with it preserves the original map on R and preserves étaleness.
-/
private theorem exists_etale_mvPolynomial_ulift {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}
    (g : MvPolynomial (Fin n) R →+* S) (hg : g.Etale) (f : R →+* S)
    (hf : g.comp MvPolynomial.C = f) :
    ∃ g' : MvPolynomial (ULift.{u} (Fin n)) R →+* S,
      g'.comp MvPolynomial.C = f ∧ g'.Etale := by
  set E : MvPolynomial (ULift.{u} (Fin n)) R ≃+* MvPolynomial (Fin n) R :=
    (MvPolynomial.renameEquiv R (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)).toRingEquiv with hE
  refine ⟨g.comp E.toRingHom, ?_, RingHom.Etale.respectsIso.right g E hg⟩
  refine RingHom.ext fun a => ?_
  have h1 : E (MvPolynomial.C a) = MvPolynomial.C a := by
    simp [hE]
  have h2 : g (MvPolynomial.C a) = f a := by rw [← hf]; rfl
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h1, h2]

/- English proof (authored)
Standard smoothness factors the ring map through an étale map from a polynomial ring over R. Reindex its variables to the index set used for affine space. Taking spectra gives an étale morphism from the spectrum of S to the spectrum of that polynomial ring, which is the relative affine space over the spectrum of R. The equality of the composite on constants becomes the required equality of maps to the base.
-/
private theorem exists_etale_over_affineSpace_of_isStandardSmooth {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (hφ : RingHom.IsStandardSmooth (CommRingCat.Hom.hom φ)) :
    ∃ (d : ℕ) (g : Spec S ⟶ AffineSpace (ULift.{u} (Fin d)) (Spec R)),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) (Spec R) ↘ Spec R) = Spec.map φ := by
  obtain ⟨n, gr, hgrC, hgrEt⟩ := hφ.exists_etale_mvPolynomial
  obtain ⟨g', hg'C, hg'Et⟩ := exists_etale_mvPolynomial_ulift gr hgrEt _ hgrC
  have hSpecEt : Etale (Spec.map (CommRingCat.ofHom g')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact hg'Et
  have hcomp : CommRingCat.ofHom (MvPolynomial.C :
      ↑R →+* MvPolynomial (ULift.{u} (Fin n)) ↑R) ≫ CommRingCat.ofHom g' = φ :=
    CommRingCat.hom_ext hg'C
  refine ⟨n, Spec.map (CommRingCat.ofHom g') ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) R).inv, inferInstance, ?_⟩
  rw [Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
  exact congrArg Spec.map hcomp

/- English proof (authored)
The canonical affine identifications turn the map of section rings into a map between the two affine opens, in the opposite direction. Its composite with the inclusion of W in X agrees with the composite of the inclusion of V with h by naturality of these identifications. The restricted scheme map has this same composite. Cancel the monomorphism given by the inclusion of W.
-/
private theorem resLE_eq_isoSpec_conj_SpecMap_appLE {X Y : Scheme.{u}} (h : Y ⟶ X) {W : X.Opens}
    {V : Y.Opens} (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W) :
    hV.isoSpec.hom ≫ Spec.map (h.appLE W V e) ≫ hW.isoSpec.inv = h.resLE W V e := by
  rw [← cancel_mono W.ι, Scheme.Hom.resLE_comp_ι]
  simp only [Category.assoc]
  rw [hW.isoSpec_inv_ι, IsAffineOpen.SpecMap_appLE_fromSpec h hW hV e, ← hV.isoSpec_inv_ι]
  simp

/- English proof (authored)
Apply the affine factorization for standard smooth ring maps to the map on sections from W to V. Transport its étale map along the affine identifications of V and W with spectra, using the induced identification of relative affine spaces over the base. Isomorphisms preserve étaleness. Naturality of the affine-space projection identifies the composite to W with the restricted map.
-/
private theorem exists_etale_over_affineSpace_resLE_of_isStandardSmooth {X Y : Scheme.{u}} (h : Y ⟶ X)
    {W : X.Opens} {V : Y.Opens}
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (e : V ≤ h ⁻¹ᵁ W)
    (hstd : RingHom.IsStandardSmooth (CommRingCat.Hom.hom (h.appLE W V e))) :
    ∃ (d : ℕ) (g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme),
      Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  obtain ⟨d, g₀, hg₀et, hg₀⟩ :=
    exists_etale_over_affineSpace_of_isStandardSmooth (h.appLE W V e) hstd
  have := hg₀et
  have : IsIso (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) :=
    ⟨⟨AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.hom, by
        rw [← AffineSpace.map_comp, Iso.inv_hom_id, AffineSpace.map_id], by
        rw [← AffineSpace.map_comp, Iso.hom_inv_id, AffineSpace.map_id]⟩⟩
  have : Etale hV.isoSpec.hom := inferInstance
  have : Etale (AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv) := inferInstance
  refine ⟨d, hV.isoSpec.hom ≫ g₀ ≫ AffineSpace.map (ULift.{u} (Fin d)) hW.isoSpec.inv,
    inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, AffineSpace.map_over, ← Category.assoc g₀, hg₀]
  exact resLE_eq_isoSpec_conj_SpecMap_appLE h hW hV e

/- English proof (authored)
Check smoothness on affine opens in the restricted source and target. Their images under the open inclusions into Y and X are affine, and the restricted map on their sections is the section-ring map of h on these images. Since h is smooth, each of these ring maps is smooth, proving the claim.
-/
private theorem smooth_resLE {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h] (W : X.Opens)
    (V : Y.Opens) (e : V ≤ h ⁻¹ᵁ W) : Smooth (h.resLE W V e) := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U U' e'
  rw [Scheme.Hom.resLE_appLE]
  exact HasRingHomProperty.appLE @Smooth h ‹Smooth h›
    ⟨W.ι ''ᵁ U.1, U.2.image_of_isOpenImmersion _⟩
    ⟨V.ι ''ᵁ U'.1, U'.2.image_of_isOpenImmersion _⟩ _

/- English proof (authored)
First restrict h to the intersection of V₀ with the inverse image of W₀, mapping that intersection to W₀. The point y belongs to the intersection and the restricted map remains smooth. Choose affine neighbourhoods of the point and its image on which the map on section rings is standard smooth. Viewed inside Y and X through the open inclusions, these are affine opens V and W with V contained in V₀, W contained in W₀, and h(V) contained in W.

The maps on sections agree under these open identifications, so the map for V and W is also standard smooth. Apply the affine factorization to obtain the étale map to a relative affine space over W. Its composite with the projection is the restriction of h, and the source open contains y.
-/
private theorem exists_affineOpen_etale_over_affineSpace_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e := by
  have e₀ : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) ≤ h ⁻¹ᵁ W₀ := inf_le_right
  have hy' : y ∈ (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens) := ⟨hV₀, hW₀⟩
  have : Smooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) := smooth_resLE h W₀ _ e₀
  obtain ⟨W', hW', V', hV', hyV', e', hstd⟩ :=
    Smooth.exists_isStandardSmooth (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀) ⟨y, hy'⟩
  have h1 : h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀ ≫ W₀.ι = (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ≫ h := by
    rw [Scheme.Hom.resLE_comp_ι]
  have hb : ∀ z : ↥(V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens),
      h.base ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι.base z)
        = W₀.ι.base ((h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z) := by
    intro z
    exact (congrArg (fun m : (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).toScheme ⟶ X => m.base z) h1).symm
  have hWle : (W₀.ι ''ᵁ W' : X.Opens) ≤ W₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2
  have hVle : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ V₀ := by
    rintro x ⟨z, -, rfl⟩
    exact z.2.1
  have e : ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) ≤ h ⁻¹ᵁ (W₀.ι ''ᵁ W') := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).base z, e' hz, (hb z).symm⟩
  have hWaff : IsAffineOpen (W₀.ι ''ᵁ W' : X.Opens) := hW'.image_of_isOpenImmersion W₀.ι
  have hVaff : IsAffineOpen ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V' : Y.Opens) :=
    hV'.image_of_isOpenImmersion _
  have happ : (h.resLE W₀ (V₀ ⊓ h ⁻¹ᵁ W₀) e₀).appLE W' V' e'
      = h.appLE (W₀.ι ''ᵁ W') ((V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V') e :=
    Scheme.Hom.resLE_appLE h e₀ W' V' e'
  rw [happ] at hstd
  obtain ⟨d, g, hg, hgπ⟩ := exists_etale_over_affineSpace_resLE_of_isStandardSmooth h hWaff hVaff e hstd
  exact ⟨W₀.ι ''ᵁ W', (V₀ ⊓ h ⁻¹ᵁ W₀ : Y.Opens).ι ''ᵁ V', d, e, hWaff, hVaff,
    ⟨⟨y, hy'⟩, hyV', rfl⟩, hWle, hVle, g, hg, hgπ⟩

/- English proof (authored)
Apply the preceding construction to the specified neighbourhoods of y and its image. It supplies the two contained affine opens, the relative affine space, and the étale factorization of the restricted map.
-/
theorem exists_isAffineOpen_etale_resLE_le {X Y : Scheme.{u}} (h : Y ⟶ X) [Smooth h]
    (y : Y) (W₀ : X.Opens) (hW₀ : h.base y ∈ W₀) (V₀ : Y.Opens) (hV₀ : y ∈ V₀) :
    ∃ (W : X.Opens) (V : Y.Opens) (d : ℕ) (e : V ≤ h ⁻¹ᵁ W),
      IsAffineOpen W ∧ IsAffineOpen V ∧ y ∈ V ∧ W ≤ W₀ ∧ V ≤ V₀ ∧
      ∃ g : V.toScheme ⟶ AffineSpace (ULift.{u} (Fin d)) W.toScheme,
        Etale g ∧
        g ≫ (AffineSpace (ULift.{u} (Fin d)) W.toScheme ↘ W.toScheme) = h.resLE W V e :=
  exists_affineOpen_etale_over_affineSpace_resLE_le h y W₀ hW₀ V₀ hV₀

end SmoothEtaleChart

end FunctorialResolution.EmbeddedResolution
