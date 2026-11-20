import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `S A _ g Y Y' e h`. Take `⟨B, b, P, hR, hG, hF⟩` from `h`. Use `⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩` and prove the remaining obligations. Introduce `T t N hN`. Take `⟨x, ⟨hx1, hx2⟩, hu⟩` from `hR.univ T (t ≫ e.inv) N hN`.

Use `⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]`. Rewrite using `[← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[Over.comp_left]`. Take `⟨hp, hs, hc⟩` from `hG`.

Establish `hi : IsIso e.hom.left` using `⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left], by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩`. Establish `hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0})` using `MorphismProperty.IsStableUnderBaseChange.respectsIso`. Use `⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩` and prove the remaining obligations. Use `smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left` as an intermediate fact. Simplify using `using this`.
-/
theorem hasRepAF_of_iso : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] (g : ℕ) {Y Y' : Over S}, (Y ≅ Y') → HasRepAF A g Y → HasRepAF A g Y' := by
  intro S A _ g Y Y' e h
  obtain ⟨B, b, P, hR, hG, hF⟩ := h
  refine ⟨B, b ≫ e.hom, P, ⟨hR.fam, ?_⟩, ?_, hF⟩
  · intro T t N hN
    obtain ⟨x, ⟨hx1, hx2⟩, hu⟩ := hR.univ T (t ≫ e.inv) N hN
    refine ⟨x, ⟨?_, hx2⟩, fun y hy => hu y ⟨?_, hy.2⟩⟩
    · rw [← Category.assoc, hx1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rw [← hy.1, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Over.comp_left]
    obtain ⟨hp, hs, hc⟩ := hG
    have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]⟩⟩
    have hR : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    refine ⟨inferInstance, ?_, MorphismProperty.RespectsIso.postcomp (@GeometricallyConnected : MorphismProperty Scheme.{0}) e.hom.left b.left hc⟩
    have := smoothOfRelativeDimension_comp (n := g) (m := 0) b.left e.hom.left
    simpa using this

end GlobalTheory
