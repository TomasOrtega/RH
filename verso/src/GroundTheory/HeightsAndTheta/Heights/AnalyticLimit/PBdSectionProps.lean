import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection)

/- English proof (translation)
Introduce `X _ D A R φ hφ c`. Take `⟨h1, h2, h3⟩` from `hφ`. Use `⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(h1 (bdIdx R x) j).add contDiffOn_const`. Take `⟨W, hW, hyW, G, hG, hGe⟩` from `h2 (bdIdx R x) (bdIdx R x') y hy`.

Use `⟨W, hW, hyW, G, hG, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h` using `hGe z ⟨hz.1.1, hz.1.2, hz.2⟩`. Use `show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) = ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))`.

Simplify using `only [neg_add, Real.exp_add, ← mul_assoc]`. Rewrite using `[h3 _ _ y hy]`. Use extensionality with `y`. Establish `h` using `(hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)`. Use `show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo`.

Rewrite using `[Ne, h, not_not]`.
-/
theorem BdSectionProps.proof (hB : BdEqHolo.Statement) : BdSectionProps.Statement := by
  intro X _ D A R φ hφ c
  obtain ⟨h1, h2, h3⟩ := hφ
  refine ⟨⟨fun x j => ?_, fun x x' y hy => ?_⟩, ⟨fun x => (hB D A R _).1, fun x x' y hy => ?_⟩, ?_⟩
  · exact (h1 (bdIdx R x) j).add contDiffOn_const
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := h2 (bdIdx R x) (bdIdx R x') y hy
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have h := hGe z ⟨hz.1.1, hz.1.2, hz.2⟩
    show (φ (bdIdx R x) z + c) - (φ (bdIdx R x') z + c) = (G z).re
    linarith
  · show ‖bdEq R (bdIdx R x) y‖ * Real.exp (-(φ (bdIdx R x) y + c)) =
      ‖bdEq R (bdIdx R x') y‖ * Real.exp (-(φ (bdIdx R x') y + c))
    simp only [neg_add, Real.exp_add, ← mul_assoc]
    rw [h3 _ _ y hy]
  · ext y
    have h := (hB D A R (bdIdx R y)).2 y (mem_bdDom_bdIdx R y)
    show bdEq R (bdIdx R y) y ≠ 0 ↔ y ∈ R.Yo
    rw [Ne, h, not_not]

end GroundTheory.Heights₂.Heights.AnalyticLimit
