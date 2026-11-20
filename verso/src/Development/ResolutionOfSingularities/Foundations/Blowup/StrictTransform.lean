import Mathlib

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FunctorialResolution.Blowup

noncomputable section

def exceptionalIdeal {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    X'.IdealSheafData :=
  Z.comap f

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem exceptionalIdeal_eq_comap {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    exceptionalIdeal f Z = Z.comap f := rfl

def strictTransformOpens {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    ((J.comap f).subscheme).Opens :=
  (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransformOpens_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformOpens f Z J =
      (J.comap f).subschemeι ⁻¹ᵁ (Z.comap f).support.compl := rfl

def strictTransformImmersion {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    (strictTransformOpens f Z J).toScheme ⟶ X' :=
  (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransformImmersion_eq {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransformImmersion f Z J =
      (strictTransformOpens f Z J).ι ≫ (J.comap f).subschemeι := rfl

def strictTransform {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    X'.IdealSheafData :=
  (strictTransformImmersion f Z J).ker

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem strictTransform_eq_ker {X' X : Scheme.{u}} (f : X' ⟶ X) (Z J : X.IdealSheafData) :
    strictTransform f Z J = (strictTransformImmersion f Z J).ker := rfl

def schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) : Y.IdealSheafData :=
  (I.subschemeι ≫ f).ker

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem schemeImageIdeal_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData) :
    schemeImageIdeal f I = (I.subschemeι ≫ f).ker := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem isClosedImmersion_lift_comp {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsClosedImmersion f] (g : Y ⟶ Z)
    (h : Scheme.Hom.ker f ≤ Scheme.Hom.ker g) : IsClosedImmersion.lift f g h ≫ f = g := by
  simp

/- English proof (translation)
Establish `hu : pullback.snd f g ≫ m ≫ ι = pullback.fst f g`. Rewrite using `[← cancel_mono f]`. Simplify using `only [Category.assoc]`. Rewrite using `[hfac, pullback.condition]`. Rewrite using `[← hu]`.

Conclude with `le_trans (Scheme.Hom.le_ker_comp m ι) (Scheme.Hom.le_ker_comp (pullback.snd f g) (m ≫ ι))`.
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

/- English proof (translation)
Rewrite using `[Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι]`. Use `le_antisymm (Scheme.IdealSheafData.comap_map_le I f) ?_` and prove the remaining obligations. Establish `hle : Scheme.Hom.ker (I.subschemeι ≫ f) ≤ Scheme.Hom.ker (I.map f).subschemeι` using `le_of_eq (by`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι])`. Establish `hcomap : (I.map f).comap f = Scheme.Hom.ker (pullback.fst f (I.map f).subschemeι)` using `rfl`.

Rewrite using `[hcomap]`. Use `le_trans (le_of_eq (Scheme.IdealSheafData.ker_subschemeι I).symm) ?_` and prove the remaining obligations. Conclude with `ker_le_ker_pullbackFst f (I.map f).subschemeι I.subschemeι (IsClosedImmersion.lift (I.subschemeι ≫ f) (I.map f).subschemeι hle) (isClosedImmersion_lift_comp (I.subschemeι ≫ f) (I.map f).subschemeι hle)`.
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

/- English proof (translation)
The claim follows from `comap_ker_subschemeι_comp f I`.
-/
theorem comap_schemeImageIdeal {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (I : X.IdealSheafData) : (schemeImageIdeal f I).comap f = I :=
  comap_ker_subschemeι_comp f I

/- English proof (translation)
Rewrite using `[strictTransform_eq_ker, strictTransformImmersion_eq]`. Establish `h` using `Scheme.Hom.le_ker_comp (strictTransformOpens p Z D).ι (D.comap p).subschemeι`. Rewrite `h` using `[Scheme.IdealSheafData.ker_subschemeι]`. Then use the resulting hypothesis.
-/
theorem comap_le_strictTransform {X X₁ : Scheme.{u}} (p : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    D.comap p ≤ strictTransform p Z D := by
  rw [strictTransform_eq_ker, strictTransformImmersion_eq]
  have h := Scheme.Hom.le_ker_comp (strictTransformOpens p Z D).ι (D.comap p).subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι] at h

end

end FunctorialResolution.Blowup
