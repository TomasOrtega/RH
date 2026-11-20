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

/- English proof (translation)
Introduce `X`. Use `infer_instance`.
-/
theorem smooth_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.id X) := by
  intro X
  infer_instance

/- English proof (translation)
Introduce `X`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Conclude with `⟨x, rfl⟩`.
-/
theorem surjective_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Surjective (CategoryTheory.CategoryStruct.id X) := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

/- English proof (translation)
Introduce `X Y Z f g I`. Simplify using the standard rewrite rules.
-/
theorem comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g) := by
  intro X Y Z f g I
  simp

/- English proof (translation)
Introduce `X Y h hsurj Z hZ`. Establish `hne : (↑Z.support : Set ↥X).Nonempty`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `he`. Conclude with `hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty Z).mpr he)`.

Take `⟨x, hx⟩` from `hne`. Take `⟨y, hy⟩` from `hsurj.1 x`. Substitute `hy` using the available equality. Use `(Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp ⟨y, ?_⟩` and prove the remaining obligations. Simplify `hx` using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`.
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

/- English proof (translation)
Introduce `T K _ f`. Establish `hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f)` using `instFlatSpecMapOfFieldHom ..`. Conclude with `MorphismProperty.of_isPullback ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip) hflat`.
-/
theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f) := instFlatSpecMapOfFieldHom ..
  exact MorphismProperty.of_isPullback
    ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip)
    hflat

/- English proof (translation)
Introduce `T K _ f`. Establish `hsurj : AlgebraicGeometry.Surjective (specMapOfFieldHom T.base K f)` using `instSurjectiveSpecMapOfFieldHom ..`. Conclude with `surjective_snd_of_isPullback_of_surjective T.structMap (CategoryTheory.Limits.pullback.snd T.structMap (specMapOfFieldHom T.base K f)) (specMapOfFieldHom T.base K f) (fieldBaseChangeProjection T K f) (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base …`.
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

/- English proof (translation)
Introduce `T K _ f I hI`. Establish `: AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f)` using `surjective_fieldBaseChangeProjection T K f`. Conclude with `comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI`.
-/
theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤ := by
  intro T K _ f I hI
  have : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI

end FunctorialResolution.EmbeddedResolution
