import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairUOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.NearSurj

/- English proof (translation)
Introduce `R _ _ U hs hsu V hV`. Establish `: Smooth (U ⊗ U).hom` using `inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))`. Take `⟨u, hu⟩` from `U.hom.surjective (closedPoint R)`. Set `d : U.left ⟶ (U ⊗ U).left` to `pullback.lift (𝟙 _) (𝟙 _) rfl`. Establish `hd : (U ⊗ U).hom (d u) = closedPoint R`.

Rewrite using `[← hu, ← Scheme.Hom.comp_apply]`. Express the relevant statement in the definitionally equal form `(pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _`. Rewrite using `[pullback.lift_fst_assoc, Category.id_comp]`. Establish `hmem : d u ∈ V` using `hV _ hd`. Establish `ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom)` using `(V.ι ≫ (U ⊗ U).hom).isOpenMap`.

Use `⟨fun r => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩ : d u ∈ Set.range V.ι` from `by rw [Scheme.Opens.range_ι]; exact hmem`. Establish `h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R`. Rewrite using `[Scheme.Hom.comp_apply, hy]`. Conclude with `hd`.

Conclude with `(IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩`.
-/
theorem surjective_of_open_closedFibre : ∀ {R : Type} [CommRing R] [IsLocalRing R] (U : Over (Sp R)), Smooth U.hom → Surjective U.hom → ∀ (V : (U ⊗ U).left.Opens), (∀ z : (U ⊗ U).left, (U ⊗ U).hom z = closedPoint R → z ∈ V) → Surjective (V.ι ≫ (U ⊗ U).hom) := by
  intro R _ _ U hs hsu V hV
  have : Smooth (U ⊗ U).hom := inferInstanceAs (Smooth (pullback.fst U.hom U.hom ≫ U.hom))
  obtain ⟨u, hu⟩ := U.hom.surjective (closedPoint R)
  let d : U.left ⟶ (U ⊗ U).left := pullback.lift (𝟙 _) (𝟙 _) rfl
  have hd : (U ⊗ U).hom (d u) = closedPoint R := by
    rw [← hu, ← Scheme.Hom.comp_apply]
    change (pullback.lift (𝟙 U.left) (𝟙 U.left) rfl ≫ pullback.fst U.hom U.hom ≫ U.hom) u = _
    rw [pullback.lift_fst_assoc, Category.id_comp]
  have hmem : d u ∈ V := hV _ hd
  have ho : IsOpenMap (V.ι ≫ (U ⊗ U).hom) := (V.ι ≫ (U ⊗ U).hom).isOpenMap
  refine ⟨fun r => ?_⟩
  obtain ⟨y, hy⟩ : d u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hmem
  have h₂ : (V.ι ≫ (U ⊗ U).hom) y = closedPoint R := by
    rw [Scheme.Hom.comp_apply, hy]; exact hd
  exact (IsLocalRing.specializes_closedPoint r).mem_open ho.isOpen_range ⟨_, h₂⟩

end GlobalTheory.Mum.NearSurj
