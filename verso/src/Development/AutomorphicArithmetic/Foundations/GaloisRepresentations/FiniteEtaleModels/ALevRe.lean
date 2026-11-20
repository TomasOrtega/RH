import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.GalOfKer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtLevZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h`. Take `⟨h1, h2, h3, h4⟩` from `id h`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y dsimp only`. Rewrite using `[h.congr (hR.add x y), h1]`.

Introduce `c x dsimp only`. Rewrite using `[h.congr (hR.lin c x), h2]`. Introduce `x hx`. Conclude with `h3 _ ((hR.ker x).mpr hx)`. Introduce `k _ _ x`.

Use `⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1`. Introduce `c hc`. Rewrite `hc` using `[pow_one]`.

Conclude with `hg c (by rw [pow_one]; exact hle hc)`. Take `⟨y0, hy0⟩` from `(h4 k x).2 g hg₁`. Take `⟨y, hy⟩` from `hR.onto y0 (by`. Introduce `c hc`. Apply `(h4 k x).1` to reduce the goal to its premises.

Rewrite using `[h2, ← Category.assoc, hy0]`. Conclude with `hg c (by rw [pow_one]; exact hc))`. Conclude with `⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.levRe_holds :
    LevRe := by
  intro q _ D R _ b N 𝔟₁ 𝔟₂ β hle hR S s o lv h
  obtain ⟨h1, h2, h3, h4⟩ := id h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    dsimp only
    rw [h.congr (hR.add x y), h1]
  · intro c x
    dsimp only
    rw [h.congr (hR.lin c x), h2]
  · intro x hx
    exact h3 _ ((hR.ker x).mpr hx)
  · intro k _ _ x
    refine ⟨fun y hy => (hR.ker y).mp ((h4 k x).1 _ hy), ?_⟩
    intro g hg
    have hg₁ : ∀ c ∈ 𝔟₁ ^ 1, g ≫ o.act.act ((algebraMap (𝓞 D.F) D.O) c) = 1 := by
      intro c hc
      rw [pow_one] at hc
      exact hg c (by rw [pow_one]; exact hle hc)
    obtain ⟨y0, hy0⟩ := (h4 k x).2 g hg₁
    obtain ⟨y, hy⟩ := hR.onto y0 (by
      intro c hc
      apply (h4 k x).1
      rw [h2, ← Category.assoc, hy0]
      exact hg c (by rw [pow_one]; exact hc))
    exact ⟨y, by dsimp only; rw [← h.congr hy, hy0]⟩
