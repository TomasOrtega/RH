import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

namespace GlobalTheory.OpenGeomIrr

/- English proof (translation)
Introduce `T W X j hj f hf hs`. Use `⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩` and prove the remaining obligations. Establish `h₁ : IrreducibleSpace ↥(Limits.pullback f x)` using `GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)`. Establish `hne : Nonempty ↥(Limits.pullback (j ≫ f) x)`. Take `⟨p⟩ : Nonempty ↥(Spec (.of K))` from `inferInstance`.

Take `⟨z, -⟩` from `(Limits.pullback.snd (j ≫ f) x).surjective p`. Conclude with `⟨z⟩`. Set `e` to `pullbackRightPullbackFstIso f x j`. Establish `hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x))` using `⟨e.inv hne.some⟩`. Establish `h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x))` using `(Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace`.

Conclude with `e.hom.homeomorph.irreducibleSpace_iff.1 h₂`.
-/
theorem geometricallyIrreducible_comp_of_isOpenImmersion : ∀ (T W X : Scheme.{0}) (j : W ⟶ X), IsOpenImmersion j →
    ∀ (f : X ⟶ T), GeometricallyIrreducible f → Surjective (j ≫ f) → GeometricallyIrreducible (j ≫ f) := by
  intro T W X j hj f hf hs
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ x => ?_⟩
  have h₁ : IrreducibleSpace ↥(Limits.pullback f x) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ (.of_hasPullback _ _)
  have hne : Nonempty ↥(Limits.pullback (j ≫ f) x) := by
    obtain ⟨p⟩ : Nonempty ↥(Spec (.of K)) := inferInstance
    obtain ⟨z, -⟩ := (Limits.pullback.snd (j ≫ f) x).surjective p
    exact ⟨z⟩
  let e := pullbackRightPullbackFstIso f x j
  have hne' : Nonempty ↥(Limits.pullback j (Limits.pullback.fst f x)) := ⟨e.inv hne.some⟩
  have h₂ : IrreducibleSpace ↥(Limits.pullback j (Limits.pullback.fst f x)) :=
    (Limits.pullback.snd j (Limits.pullback.fst f x)).isOpenEmbedding.irreducibleSpace
  exact e.hom.homeomorph.irreducibleSpace_iff.1 h₂

end GlobalTheory.OpenGeomIrr
