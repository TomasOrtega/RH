import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIsoSpecMvPolynomial (k : Type u) [Field k] (v : Type u) :
    affineSpaceIndexedBy k v ≅ Spec (CommRingCat.of (MvPolynomial v k)) :=
  AffineSpace.SpecIso v (CommRingCat.of k)

def mvPolynomialToGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k →+* Γ(affineSpaceIndexedBy k v, ⊤) :=
  ((affineSpaceIsoSpecMvPolynomial k v).hom.appTop).hom.comp
    ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv).hom

def globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Γ(affineSpaceIndexedBy k v, ⊤) →+* MvPolynomial v k :=
  ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom).hom.comp
    ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop).hom

/- English proof (authored)
Pulling back along the isomorphism and then along its inverse is pullback along their identity composite. The section is therefore unchanged.
-/
private theorem appTop_inv_hom_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(Y, ⊤)) :
    e.inv.appTop (e.hom.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
  simp

/- English proof (authored)
The two pullbacks compose to pullback along the identity on the other scheme, since the forward map and its inverse compose to that identity.
-/
private theorem appTop_hom_inv_apply {X Y : Scheme.{u}} (e : X ≅ Y) (s : Γ(X, ⊤)) :
    e.hom.appTop (e.inv.appTop s) = s := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
  simp

/- English proof (authored)
The map first regards the polynomial as a global section of its spectrum, then pulls it back along the affine-space isomorphism.
-/
private theorem mvPolynomialToGlobalSections_apply (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    mvPolynomialToGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

/- English proof (authored)
Pull the affine-space section back to the polynomial spectrum along the inverse isomorphism. The identification of sections on a spectrum with its ring then gives the corresponding polynomial.
-/
private theorem globalSectionsToMvPolynomial_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    globalSectionsToMvPolynomial k v s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

/- English proof (authored)
Starting with a polynomial, the two maps first identify it with a section on its spectrum, then successively pull back along the forward and inverse scheme isomorphisms. Those pullbacks cancel. Returning from sections on the spectrum to polynomials recovers the original polynomial.
-/
theorem leftInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.LeftInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro p
  rw [mvPolynomialToGlobalSections_apply, globalSectionsToMvPolynomial_apply, appTop_inv_hom_apply]
  simp

/- English proof (authored)
Starting with a section, pull it back to the spectrum and regard it as a polynomial. The forward map reverses the identification of sections on the spectrum with polynomials, then pulls back along the inverse of the first pullback. The result is the original section.
-/
theorem rightInverse_globalSectionsToMvPolynomial (k : Type u) [Field k] (v : Type u) :
    Function.RightInverse ⇑(globalSectionsToMvPolynomial k v) ⇑(mvPolynomialToGlobalSections k v) := by
  intro s
  rw [globalSectionsToMvPolynomial_apply, mvPolynomialToGlobalSections_apply, Iso.hom_inv_id_apply,
    appTop_hom_inv_apply]

def mvPolynomialEquivGlobalSections (k : Type u) [Field k] (v : Type u) :
    MvPolynomial v k ≃+* Γ(affineSpaceIndexedBy k v, ⊤) where
  toFun := mvPolynomialToGlobalSections k v
  invFun := globalSectionsToMvPolynomial k v
  left_inv := leftInverse_globalSectionsToMvPolynomial k v
  right_inv := rightInverse_globalSectionsToMvPolynomial k v
  map_mul' := map_mul (mvPolynomialToGlobalSections k v)
  map_add' := map_add (mvPolynomialToGlobalSections k v)

/- English proof (authored)
The forward map of the equivalence is the polynomial-to-section map. It identifies the polynomial with a section on the spectrum and pulls back along the affine-space isomorphism.
-/
theorem mvPolynomialEquivGlobalSections_apply (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    mvPolynomialEquivGlobalSections k v p =
      (affineSpaceIsoSpecMvPolynomial k v).hom.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := rfl

/- English proof (authored)
The inverse of the equivalence uses the section-to-polynomial map. It transfers the section to the spectrum along the inverse affine-space isomorphism and then identifies it with a polynomial.
-/
theorem mvPolynomialEquivGlobalSections_symm_apply (k : Type u) [Field k] (v : Type u)
    (s : Γ(affineSpaceIndexedBy k v, ⊤)) :
    (mvPolynomialEquivGlobalSections k v).symm s =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).hom
        ((affineSpaceIsoSpecMvPolynomial k v).inv.appTop s) := rfl

/- English proof (authored)
The affine-space isomorphism with the polynomial spectrum gives the universal coordinate sections on that spectrum. Pulling the specified coordinate back along its inverse gives the section of the corresponding polynomial variable.
-/
private theorem affineSpaceIsoSpecMvPolynomial_inv_appTop_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (affineSpaceIsoSpecMvPolynomial k v).inv.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.X i) := by
  rw [AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord]

@[simp]
/- English proof (authored)
The section of the polynomial variable on the spectrum is the pullback of the corresponding affine coordinate along the inverse isomorphism. The forward polynomial-to-section map pulls it back along the opposite isomorphism, recovering that coordinate.
-/
theorem mvPolynomialEquivGlobalSections_X (k : Type u) [Field k] (v : Type u) (i : v) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.X i) = AffineSpace.coord (Spec (CommRingCat.of k)) i := by
  rw [mvPolynomialEquivGlobalSections_apply, ← affineSpaceIsoSpecMvPolynomial_inv_appTop_coord k v i, appTop_hom_inv_apply]

@[simp]
/- English proof (authored)
The forward equivalence sends the specified polynomial variable to the coordinate section. Applying the inverse returns that variable.
-/
theorem mvPolynomialEquivGlobalSections_symm_coord (k : Type u) [Field k] (v : Type u) (i : v) :
    (mvPolynomialEquivGlobalSections k v).symm (AffineSpace.coord (Spec (CommRingCat.of k)) i) =
      MvPolynomial.X i := by
  rw [← mvPolynomialEquivGlobalSections_X k v i, RingEquiv.symm_apply_apply]

/- English proof (authored)
On the polynomial spectrum the structural map to the field spectrum is induced by the inclusion of constants. By naturality of the identification of a ring with sections on its spectrum, pulling back a field element along this map gives the section corresponding to the constant polynomial. Transfer this equality to affine space using the isomorphism over the field.
-/
theorem mvPolynomialEquivGlobalSections_C (k : Type u) [Field k] (v : Type u) (c : k) :
    mvPolynomialEquivGlobalSections k v (MvPolynomial.C c) =
      (affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [mvPolynomialEquivGlobalSections_apply]
  have h2 : (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial v k))).appTop :=
    Scheme.ΓSpecIso_inv_naturality _
  have key : (affineSpaceIsoSpecMvPolynomial k v).inv.appTop
      ((affineSpaceIndexedByToSpec k v).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) =
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv (MvPolynomial.C c) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    simp
    rw [← CommRingCat.comp_apply, ← h2, CommRingCat.comp_apply]
    simp
  rw [← key, appTop_hom_inv_apply]

/- English proof (authored)
The section associated to the polynomial is pulled back from the polynomial spectrum along the affine-space isomorphism. A basic open for a pulled-back section is the inverse image of the basic open for the original section.
-/
theorem mvPolynomialEquivGlobalSections_basicOpen (k : Type u) [Field k] (v : Type u) (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (Spec (CommRingCat.of (MvPolynomial v k))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial v k))).inv p) := by
  rw [mvPolynomialEquivGlobalSections_apply, Scheme.preimage_basicOpen]
  rfl

/- English proof (authored)
The basic open of the section on the polynomial spectrum is exactly the prime-spectrum basic open of its corresponding polynomial. Substitute this in the inverse-image formula.
-/
theorem mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum (k : Type u) [Field k] (v : Type u)
    (p : MvPolynomial v k) :
    (affineSpaceIndexedBy k v).basicOpen (mvPolynomialEquivGlobalSections k v p) =
      (affineSpaceIsoSpecMvPolynomial k v).hom ⁻¹ᵁ
        (PrimeSpectrum.basicOpen p : Opens (PrimeSpectrum (MvPolynomial v k))) := by
  rw [mvPolynomialEquivGlobalSections_basicOpen, basicOpen_eq_of_affine]

end FunctorialResolution.EmbeddedResolution

end
