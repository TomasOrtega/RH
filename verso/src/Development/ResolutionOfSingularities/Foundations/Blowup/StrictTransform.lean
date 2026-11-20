import Mathlib

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

noncomputable section

def exceptionalIdeal {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    X'.IdealSheafData :=
  Z.comap f

/- English proof (authored)
The exceptional ideal is defined to be the pullback of the center ideal along the blowup.
-/
theorem exceptionalIdeal_eq_comap {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    exceptionalIdeal f Z = Z.comap f := rfl

def strictTransformOpens {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    ((J.comap f).subscheme).Opens :=
  (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl

/- English proof (authored)
In the closed subscheme of the total transform, the defining open for the strict transform is the inverse image of the complement of the exceptional support.
-/
theorem strictTransformOpens_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformOpens f Z J =
      (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl := rfl

def strictTransformImmersion {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    (strictTransformOpens f Z J).toScheme ⟶ X' :=
  (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι

/- English proof (authored)
The defining map first includes the open part in the total-transform closed subscheme, then includes that subscheme in the blowup scheme.
-/
theorem strictTransformImmersion_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformImmersion f Z J =
      (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι := rfl

def strictTransform {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    X'.IdealSheafData :=
  (strictTransformImmersion f Z J).ker

/- English proof (authored)
The strict-transform ideal is the ideal of the scheme-theoretic image of the open part off the exceptional support. By definition it is the kernel of the map from this open part to the blowup scheme.
-/
theorem strictTransform_eq_ker {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := rfl

def schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker

/- English proof (authored)
The image ideal of the subscheme is the scheme-theoretic kernel of its inclusion followed by the given morphism.
-/
theorem schemeImageIdeal_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    schemeImageIdeal f I = (I.subschemeι ≫ f).ker := rfl

/- English proof (authored)
The lift through the closed immersion is defined to factor the given map. The defining identity says that its composite with the immersion is the given map.
-/
private theorem isClosedImmersion_lift_comp {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z)
    (h : Scheme.Hom.ker f ≤ Scheme.Hom.ker g) : IsClosedImmersion.lift f g h ≫ f = g := by
  simp

/- English proof (authored)
The map from the pullback to the intermediate scheme, followed by the given factorization to the first source, has the same composite to the base as the first projection. Cancel the monomorphism to identify it with that projection. Thus the projection factors through the indicated morphism to the first source, whose kernel is contained in the kernel of the projection.
-/
private theorem ker_le_ker_pullbackFst {X Y W Z : Scheme.{u}} (f : X ⟶ Y) [Mono f] (g : Z ⟶ Y)
    (ι : W ⟶ X) (m : Z ⟶ W) (hfac : m ≫ ι ≫ f = g) :
    Scheme.Hom.ker ι ≤ Scheme.Hom.ker (pullback.fst f g) := by
  have hu : pullback.snd f g ≫ m ≫ ι = pullback.fst f g := by
    rw [← cancel_mono f]
    simp only [Category.assoc]
    rw [hfac, pullback.condition]
  rw [← hu]
  exact le_trans (Scheme.Hom.le_ker_comp m ι)
    (Scheme.Hom.le_ker_comp (pullback.snd f g) (m ≫ ι))

/- English proof (authored)
The kernel of the composite is the image ideal, so pulling it back gives an ideal contained in the original one by the general image-pullback inequality. For the other containment, its closed-subscheme inclusion factors through the original composite closed immersion because the kernels agree. The projection in the pullback defining the pullback ideal then factors through the original subscheme inclusion, using the monomorphism into the ambient target. Its kernel contains the original ideal, proving equality.
-/
theorem comap_ker_subschemeι_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le I f) ?_
  have hle : Scheme.Hom.ker (I.subschemeι ≫ f) ≤ Scheme.Hom.ker (I.map f).subschemeι :=
    le_of_eq (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        Scheme.IdealSheafData.ker_subschemeι])
  have hcomap : (I.map f).comap f =
      Scheme.Hom.ker (pullback.fst f (I.map f).subschemeι) := rfl
  rw [hcomap]
  refine le_trans (le_of_eq (Scheme.IdealSheafData.ker_subschemeι I).symm) ?_
  exact ker_le_ker_pullbackFst f (I.map f).subschemeι I.subschemeι
    (IsClosedImmersion.lift (I.subschemeι ≫ f) (I.map f).subschemeι hle)
    (isClosedImmersion_lift_comp (I.subschemeι ≫ f) (I.map f).subschemeι hle)

/- English proof (authored)
The scheme image ideal is the kernel of the subscheme inclusion followed by the given closed immersion. Pulling this kernel back recovers the original ideal by the closed-immersion kernel formula.
-/
theorem comap_schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : X.IdealSheafData) : (schemeImageIdeal f I).comap f = I :=
  comap_ker_subschemeι_comp f I

/- English proof (authored)
The strict-transform map factors through the closed subscheme of the total transform. Every section in the kernel of that closed immersion therefore vanishes under the strict-transform map. The kernels are respectively the total-transform ideal and the strict-transform ideal.
-/
theorem comap_le_strictTransform {X X₁ : Scheme.{u}} (p : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    D.comap p ≤ strictTransform p Z D := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq]
  have h := Scheme.Hom.le_ker_comp (strictTransformOpens p Z D).ι (D.comap p).subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

end

end FunctorialResolution.Blowup
