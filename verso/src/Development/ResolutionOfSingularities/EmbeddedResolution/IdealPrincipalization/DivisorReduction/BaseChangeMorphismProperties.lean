import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The identity of a scheme is an isomorphism. An isomorphism is smooth.
-/
theorem smooth_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.id X) := by
  intro X
  infer_instance

/- English proof (authored)
For each point of the target, the same point in the source maps to it under the identity. Hence the map is surjective.
-/
theorem surjective_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Surjective (CategoryTheory.CategoryStruct.id X) := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

/- English proof (authored)
Pullback of ideal sheaves is contravariantly functorial. Pulling the ideal back along the second morphism and then the first therefore equals pullback along their composite.
-/
theorem comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g) := by
  intro X Y Z f g I
  simp

/- English proof (authored)
A nonunit ideal has a point in its support. Surjectivity lifts this point to the source, and the support of the pullback ideal is the inverse image of the original support. Thus that support is nonempty and the pullback ideal is nonunit.
-/
theorem comap_ne_top_of_surjective :
    ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData),
      Z ≠ ⊤ → Z.comap h ≠ ⊤ := by
  intro X Y h hsurj Z hZ
  have hne : (↑Z.support : Set ↥X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty Z).mpr he)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hsurj.1 x
  subst hy
  refine (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp ⟨y, ?_⟩
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using hx

/- English proof (authored)
A field extension is flat as an algebra over the original field, so its map of spectra is flat. The stated projection is the base change of this map along the original structure morphism. Flatness is stable under base change.
-/
theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f) := instFlatSpecMapOfFieldHom ..
  exact MorphismProperty.of_isPullback
    ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip)
    hflat

/- English proof (authored)
The two field spectra each have a single point, so the map of spectra is surjective. The projection of the base change is its pullback, which preserves surjectivity.
-/
theorem surjective_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hsurj : AlgebraicGeometry.Surjective (specMapOfFieldHom T.base K f) :=
    instSurjectiveSpecMapOfFieldHom ..
  exact surjective_snd_of_isPullback_of_surjective T.structMap
    (CategoryTheory.Limits.pullback.snd T.structMap (specMapOfFieldHom T.base K f))
    (specMapOfFieldHom T.base K f) (fieldBaseChangeProjection T K f)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip

/- English proof (authored)
The field-extension projection is surjective. The general support argument for pullback along a surjective morphism therefore shows that a nonunit ideal remains nonunit.
-/
theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤ := by
  intro T K _ f I hI
  have : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI

end FunctorialResolution.EmbeddedResolution
