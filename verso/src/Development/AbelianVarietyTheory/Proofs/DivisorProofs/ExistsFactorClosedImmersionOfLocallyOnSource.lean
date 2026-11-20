import Mathlib
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `Z A Y a ha g h`. Use `choose W hW z hz using h`. Establish `hc : TopologicalSpace.IsOpenCover W`. Use `TopologicalSpace.IsOpenCover.mk ?_` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Conclude with `TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩`. Set `𝒰` to `Y.openCoverOfIsOpenCover W hc`. Take `⟨u, hu⟩ : ∃ u : ∀ i, 𝒰.X i ⟶ A, ∀ i, u i ≫ a = 𝒰.f i ≫ g` from `⟨z, hz⟩`. Establish `hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j`.

Introduce `i j`. Rewrite using `[← cancel_mono a, Category.assoc, Category.assoc, hu, hu, pullback.condition_assoc]`. Use `⟨𝒰.glueMorphisms u hglue, ?_⟩` and prove the remaining obligations. Use `𝒰.hom_ext _ _ fun i => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, Scheme.Cover.ι_glueMorphisms]`.

Conclude with `hu i`.
-/
theorem exists_factor_closedImmersion_of_locally :
    ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z),
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) →
      ∃ z : Y ⟶ A, z ≫ a = g := by
  intro Z A Y a ha g h
  choose W hW z hz using h
  have hc : TopologicalSpace.IsOpenCover W := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro y _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hW y⟩
  let 𝒰 := Y.openCoverOfIsOpenCover W hc
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, 𝒰.X i ⟶ A, ∀ i, u i ≫ a = 𝒰.f i ≫ g := ⟨z, hz⟩
  have hglue : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ u i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ u j := by
    intro i j
    rw [← cancel_mono a, Category.assoc, Category.assoc, hu, hu, pullback.condition_assoc]
  refine ⟨𝒰.glueMorphisms u hglue, ?_⟩
  refine 𝒰.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
  exact hu i

end GlobalTheory
