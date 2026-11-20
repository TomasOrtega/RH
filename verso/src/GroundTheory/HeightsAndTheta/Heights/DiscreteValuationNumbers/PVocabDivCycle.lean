import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `R _ _ K _ ι _ P s W`. Establish `e : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]`. Rewrite using `[e, divCycle]`. Distinguish the cases in `h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s`.

Establish `h' : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W` using `h`. Establish `hW : W.IsPrime` using `h'.1.1.1`. Rewrite using `[if_pos h, dif_pos h', ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hW]`. Both sides reduce to the same expression. Establish `h' : ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W)` using `h`.

Rewrite using `[if_neg h, dif_neg h']`. Both sides reduce to the same expression.
-/
theorem VocabDivCycle.proof : VocabDivCycle.Statement := by
  intro R _ _ K _ ι _ P s W
  classical
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [e, divCycle]
  by_cases h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s
  · have h' : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := h
    have hW : W.IsPrime := h'.1.1.1
    rw [if_pos h, dif_pos h', ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hW]
    rfl
  · have h' : ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W) := h
    rw [if_neg h, dif_neg h']
    rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
