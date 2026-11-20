import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
It suffices to establish `IsDominant (equalizer.ι f g) from ext_of_isDominant_of_isSeparated t h (equalizer.ι f g) (equalizer.condition _ _)`. Use `⟨Dense.mono (fun x hx ↦ ?_) hD⟩` and prove the remaining obligations. Set `K` to `AlgebraicClosure (X.residueField x)`. Set `y : Sp K ⟶ X` to `Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x`. Establish `hy : ∀ p, y p = x` using `fun p ↦ Scheme.fromSpecResidueField_apply x _`.

Establish `hxy : y ≫ f = y ≫ g` using `H K y (by rintro _ ⟨p, rfl⟩; rwa [hy])`. Establish `p : Sp K` using `IsLocalRing.closedPoint K`. Use `⟨equalizer.lift y hxy p, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, equalizer.lift_ι, hy]`.
-/
theorem hom_ext_of_geometricPoints_dense {X Y S : Scheme.{0}} [IsReduced X] (t : Y ⟶ S)
    [IsSeparated t] (f g : X ⟶ Y) (h : f ≫ t = g ≫ t) (D : Set X) (hD : Dense D)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.range x ⊆ D →
      x ≫ f = x ≫ g) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated t h (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨Dense.mono (fun x hx ↦ ?_) hD⟩
  let K := AlgebraicClosure (X.residueField x)
  let y : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
  have hy : ∀ p, y p = x := fun p ↦ Scheme.fromSpecResidueField_apply x _
  have hxy : y ≫ f = y ≫ g := H K y (by rintro _ ⟨p, rfl⟩; rwa [hy])
  have p : Sp K := IsLocalRing.closedPoint K
  refine ⟨equalizer.lift y hxy p, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, hy]

/- English proof (translation)
Establish `: IsDominant (pullback.snd i f)` using `⟨Dense.mono (fun x hx ↦ by`. Rewrite using `[Scheme.Pullback.range_snd]`. Conclude with `H x hx) hD⟩`. Establish `: Surjective (pullback.snd i f)` using `surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range`. Use `isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)` as an intermediate fact.

Use `⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]`.
-/
theorem exists_lift_closedImmersion_of_dense {X Y Z : Scheme.{0}} [IsReduced X] (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : X ⟶ Y) (D : Set X) (hD : Dense D)
    (H : ∀ x ∈ D, f x ∈ Set.range i) : ∃ f' : X ⟶ Z, f' ≫ i = f := by
  have : IsDominant (pullback.snd i f) := ⟨Dense.mono (fun x hx ↦ by
    rw [Scheme.Pullback.range_snd]; exact H x hx) hD⟩
  have : Surjective (pullback.snd i f) :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

/- English proof (translation)
Introduce `X S _ s _ _ Sg hSg`. Establish `hD : Dense (s ⁻¹' Sg)` using `hSg.preimage s.isOpenMap`. Use `⟨hD, fun Y t _ f g hf hg H ↦ ?_, fun Y Z i _ f H ↦ ?_⟩` and prove the remaining obligations. Use `hom_ext_of_geometricPoints_dense t f g (hf.trans hg.symm) _ hD fun K _ _ x hx ↦ ?_` and prove the remaining obligations. Use `H K x ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hx ⟨p, rfl⟩`. Conclude with `exists_lift_closedImmersion_of_dense i f _ hD H`.
-/
theorem dense_fibres_ext :
    ∀ (X S : Scheme.{0}) [IsReduced X] (s : X ⟶ S) [Flat s] [LocallyOfFinitePresentation s]
      (Sg : Set S), Dense Sg → Dense (s ⁻¹' Sg) ∧
      (∀ (Y : Scheme.{0}) (t : Y ⟶ S) [IsSeparated t] (f g : X ⟶ Y), f ≫ t = s → g ≫ t = s →
        (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
          Set.range (x ≫ s) ⊆ Sg → x ≫ f = x ≫ g) → f = g) ∧
      (∀ (Y Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y),
        (∀ x : X, s x ∈ Sg → f x ∈ Set.range i) → ∃ f' : X ⟶ Z, f' ≫ i = f) := by
  intro X S _ s _ _ Sg hSg
  have hD : Dense (s ⁻¹' Sg) := hSg.preimage s.isOpenMap
  refine ⟨hD, fun Y t _ f g hf hg H ↦ ?_, fun Y Z i _ f H ↦ ?_⟩
  · refine hom_ext_of_geometricPoints_dense t f g (hf.trans hg.symm) _ hD fun K _ _ x hx ↦ ?_
    refine H K x ?_
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hx ⟨p, rfl⟩
  · exact exists_lift_closedImmersion_of_dense i f _ hD H

end GlobalTheory
