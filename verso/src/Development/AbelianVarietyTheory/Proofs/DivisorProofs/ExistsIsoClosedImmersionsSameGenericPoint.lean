import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
open Limits

namespace GlobalTheory

/- English proof (translation)
Establish `hc : IsClosedMap i` using `i.isClosedEmbedding.isClosedMap`. Establish `h1 : Set.range i = i '' closure {genericPoint Y}`. Rewrite using `[(genericPoint_spec Y).def, Set.image_univ]`. Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `image_closure_subset_closure_image i.continuous |>.trans (by rw [Set.image_singleton])`. Rewrite using `[← Set.image_singleton]`. Conclude with `closure_minimal (Set.image_mono subset_closure) (hc _ isClosed_closure)`.
-/
theorem range_closedImmersion_eq_closure_genericPoint {X Y : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] : Set.range i = closure {i (genericPoint Y)} := by
  have hc : IsClosedMap i := i.isClosedEmbedding.isClosedMap
  have h1 : Set.range i = i '' closure {genericPoint Y} := by
    rw [(genericPoint_spec Y).def, Set.image_univ]
  rw [h1]
  apply le_antisymm
  · exact image_closure_subset_closure_image i.continuous |>.trans (by rw [Set.image_singleton])
  · rw [← Set.image_singleton]
    exact closure_minimal (Set.image_mono subset_closure) (hc _ isClosed_closure)

/- English proof (translation)
Introduce `X Y Y' _ _ i i' _ _ h`. Establish `hr : Set.range i = Set.range i'`. Rewrite using `[range_closedImmersion_eq_closure_genericPoint, range_closedImmersion_eq_closure_genericPoint, h]`. Establish `hs : Function.Surjective (pullback.snd i i')`. Introduce `y'`.

Take `⟨y, hy⟩ : i' y' ∈ Set.range i` from `hr ▸ ⟨y', rfl⟩`. Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy`. Conclude with `⟨z, hz⟩`. Establish `hf : Function.Surjective (pullback.fst i i')`. Introduce `y`.

Take `⟨y', hy⟩ : i y ∈ Set.range i'` from `hr ▸ ⟨y, rfl⟩`. Take `⟨z, hz, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy.symm`. Conclude with `⟨z, hz⟩`. Use `haveI : Surjective (pullback.snd i i') := ⟨hs⟩`. Use `haveI : Surjective (pullback.fst i i') := ⟨hf⟩`.

Use `haveI : IsIso (pullback.snd i i') := isIso_of_isClosedImmersion_of_surjective _`. Use `haveI : IsIso (pullback.fst i i') := isIso_of_isClosedImmersion_of_surjective _`. Use `⟨inv (pullback.snd i i') ≫ pullback.fst i i', inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]`. Apply `i.isClosedEmbedding.injective` to reduce the goal to its premises.

Establish `e` using `congrArg (fun f : Y' ⟶ X => f (genericPoint Y')) (show (inv (pullback.snd i i') ≫ pullback.fst i i') ≫ i = i' by`. Rewrite using `[Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])`. Rewrite `e` using `[Scheme.Hom.comp_apply]`. Rewrite using `[e, h]`.
-/
theorem iso_of_closedImmersion_genericPoint_eq :
    ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X)
      [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') →
      ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  intro X Y Y' _ _ i i' _ _ h
  have hr : Set.range i = Set.range i' := by
    rw [range_closedImmersion_eq_closure_genericPoint, range_closedImmersion_eq_closure_genericPoint, h]
  have hs : Function.Surjective (pullback.snd i i') := by
    intro y'
    obtain ⟨y, hy⟩ : i' y' ∈ Set.range i := hr ▸ ⟨y', rfl⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy
    exact ⟨z, hz⟩
  have hf : Function.Surjective (pullback.fst i i') := by
    intro y
    obtain ⟨y', hy⟩ : i y ∈ Set.range i' := hr ▸ ⟨y, rfl⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := i') y y' hy.symm
    exact ⟨z, hz⟩
  haveI : Surjective (pullback.snd i i') := ⟨hs⟩
  haveI : Surjective (pullback.fst i i') := ⟨hf⟩
  haveI : IsIso (pullback.snd i i') := isIso_of_isClosedImmersion_of_surjective _
  haveI : IsIso (pullback.fst i i') := isIso_of_isClosedImmersion_of_surjective _
  refine ⟨inv (pullback.snd i i') ≫ pullback.fst i i', inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
  · apply i.isClosedEmbedding.injective
    have e := congrArg (fun f : Y' ⟶ X => f (genericPoint Y')) (show (inv (pullback.snd i i') ≫ pullback.fst i i') ≫ i = i' by
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc])
    rw [Scheme.Hom.comp_apply] at e
    rw [e, h]

end GlobalTheory
