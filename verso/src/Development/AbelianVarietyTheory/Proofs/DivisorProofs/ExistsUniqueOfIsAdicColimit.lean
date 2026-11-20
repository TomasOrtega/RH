import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfDisjointCover
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitFiniteHenselianOfLocal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient

open CategoryTheory AlgebraicGeometry Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AdicColimit

namespace GlobalTheory.FinitePointLimit

/- English proof (translation)
Establish `hι : ∀ e : ℕ, thickι J e (Over.mk (𝟙 (Sp B))) = pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thick B J e`. Introduce `e`. Establish `hc` using `pullback.condition (f := (Over.mk (𝟙 (Sp B))).hom) (g := Out.thick B J e)`. Use `show pullback.fst _ _ = _`. Simplify using `using hc`.

Establish `hiso : ∀ e : ℕ, IsIso (pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e))`. Introduce `e`. Establish `: IsIso (Over.mk (𝟙 (Sp B))).hom` using `by show IsIso (𝟙 _) infer_instance`. Use `infer_instance`. Establish `hmap : ∀ e : ℕ, Out.thickMap B J e (Over.mk (𝟙 (Sp B))) ≫ pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J (e + 1)) = pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thickTrans B J e`.

Introduce `e`. Rewrite using `[← cancel_mono (Out.thick B J (e + 1)), Category.assoc, Category.assoc, Out.thickTrans_comp, ← hι, ← hι, thickMap_ι]`. Take `⟨g, hg, hu⟩` from `h X (fun e => pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ z e) (by`. Introduce `e`. Rewrite using `[← Category.assoc, hmap, Category.assoc, hz])`.

Use `⟨g, fun e => ?_, fun x hx => hu x fun e => ?_⟩` and prove the remaining obligations. Establish `he` using `hg e`. Rewrite `he` using `[hι, Category.assoc]`. Use `hiso e` as an intermediate fact. Conclude with `(cancel_epi _).mp he`.

Rewrite using `[hι, Category.assoc, hx]`.
-/
theorem existsUnique_of_isAdicColimit {B : Type} [CommRing B] (J : Ideal B)
    (h : IsAdicColimit J (Over.mk (𝟙 (Sp B)))) (X : Scheme.{0}) (z : ∀ e : ℕ, Sp (B ⧸ J ^ (e + 1)) ⟶ X)
    (hz : ∀ e : ℕ, Out.thickTrans B J e ≫ z (e + 1) = z e) :
    ∃! x : Sp B ⟶ X, ∀ e : ℕ, Out.thick B J e ≫ x = z e := by
  have hι : ∀ e : ℕ, thickι J e (Over.mk (𝟙 (Sp B))) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thick B J e := by
    intro e
    have hc := pullback.condition (f := (Over.mk (𝟙 (Sp B))).hom) (g := Out.thick B J e)
    show pullback.fst _ _ = _
    simpa using hc
  have hiso : ∀ e : ℕ, IsIso (pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e)) := by
    intro e
    have : IsIso (Over.mk (𝟙 (Sp B))).hom := by
      show IsIso (𝟙 _)
      infer_instance
    infer_instance
  have hmap : ∀ e : ℕ, Out.thickMap B J e (Over.mk (𝟙 (Sp B))) ≫
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J (e + 1)) =
      pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ Out.thickTrans B J e := by
    intro e
    rw [← cancel_mono (Out.thick B J (e + 1)), Category.assoc, Category.assoc,
      Out.thickTrans_comp, ← hι, ← hι, thickMap_ι]
  obtain ⟨g, hg, hu⟩ := h X
    (fun e => pullback.snd (Over.mk (𝟙 (Sp B))).hom (Out.thick B J e) ≫ z e) (by
      intro e
      rw [← Category.assoc, hmap, Category.assoc, hz])
  refine ⟨g, fun e => ?_, fun x hx => hu x fun e => ?_⟩
  · have he := hg e
    rw [hι, Category.assoc] at he
    have := hiso e
    exact (cancel_epi _).mp he
  · rw [hι, Category.assoc, hx]

end GlobalTheory.FinitePointLimit
