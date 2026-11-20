import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F I _ _ I' _ _ L G c hL hc n`. Take `⟨h1, h2⟩` from `hc n`. Use `⟨fun x => ?_, fun i y hy => ?_⟩` and prove the remaining obligations. Take `⟨i', y, hy⟩` from `h1 x`. Conclude with `⟨L.obj i', y, hy⟩`.

Take `⟨i', ⟨f⟩⟩` from `hL i`. Establish `hy' : pull R ((c.whisker L).π.app i') F n (pull R (G.map f) F n y) = 0`. Express the relevant statement in the definitionally equal form `pull R (c.π.app (L.obj i')) F n (pull R (G.map f) F n y) = 0`. Rewrite using `[← pull_comp, c.w f]`. Conclude with `hy`.

Take `⟨k', g, hg⟩` from `h2 i' _ hy'`. Use `⟨L.obj k', L.map g ≫ f, ?_⟩` and prove the remaining obligations. Rewrite using `[Functor.map_comp, pull_comp]`. Conclude with `hg`.
-/
theorem contCone_of_whisker : ∀ (R : Type) [CommRing R] (F : Shv R) (I : Type) [SmallCategory I] [IsCofiltered I] (I' : Type) [SmallCategory I'] [IsCofiltered I'] (L : I' ⥤ I) (G : I ⥤ Spc) (c : Cone G), (∀ i, ∃ i', Nonempty (L.obj i' ⟶ i)) → ContCone R F (c.whisker L) → ContCone R F c := by
  intro R _ F I _ _ I' _ _ L G c hL hc n
  obtain ⟨h1, h2⟩ := hc n
  refine ⟨fun x => ?_, fun i y hy => ?_⟩
  · obtain ⟨i', y, hy⟩ := h1 x
    exact ⟨L.obj i', y, hy⟩
  · obtain ⟨i', ⟨f⟩⟩ := hL i
    have hy' : pull R ((c.whisker L).π.app i') F n (pull R (G.map f) F n y) = 0 := by
      change pull R (c.π.app (L.obj i')) F n (pull R (G.map f) F n y) = 0
      rw [← pull_comp, c.w f]
      exact hy
    obtain ⟨k', g, hg⟩ := h2 i' _ hy'
    refine ⟨L.obj k', L.map g ≫ f, ?_⟩
    rw [Functor.map_comp, pull_comp]
    exact hg

end GlobalTheory.EtC
