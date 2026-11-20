import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `k _`. Set `v` to `(Polynomial.idealX k).valuation (RatFunc k)`. Establish `hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring`. Introduce `a`. Rewrite using `[Valuation.mem_valuationSubring_iff, IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]`.

Conclude with `(Polynomial.idealX k).valuation_le_one _`. Establish `hX : v RatFunc.X < 1`. Rewrite using `[← RatFunc.algebraMap_X]`. Conclude with `((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by`. Rewrite using `[Polynomial.idealX_span]`.

Conclude with `Ideal.mem_span_singleton_self _)`. Establish `hX' : RatFunc.X ∈ v.valuationSubring`. Rewrite using `[Valuation.mem_valuationSubring_iff]`. Conclude with `hX.le`. Use `⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc, ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Both sides reduce to the same expression. Rewrite using `[IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]`. Conclude with `((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX`.
-/
theorem exists_valuationSubring_ratFunc_residue_X_eq_zero :
    ∀ (k : Type) [Field k], ∃ (V : ValuationSubring (RatFunc k)) (c : k →+* V) (t : V), (algebraMap V (RatFunc k)).comp c = algebraMap k (RatFunc k) ∧ (t : RatFunc k) = RatFunc.X ∧ IsLocalRing.residue V t = 0 := by
  intro k _
  let v := (Polynomial.idealX k).valuation (RatFunc k)
  have hc : ∀ a : k, algebraMap k (RatFunc k) a ∈ v.valuationSubring := by
    intro a
    rw [Valuation.mem_valuationSubring_iff,
      IsScalarTower.algebraMap_apply k (Polynomial k) (RatFunc k)]
    exact (Polynomial.idealX k).valuation_le_one _
  have hX : v RatFunc.X < 1 := by
    rw [← RatFunc.algebraMap_X]
    exact ((Polynomial.idealX k).valuation_lt_one_iff_mem _).2 (by
      rw [Polynomial.idealX_span]; exact Ideal.mem_span_singleton_self _)
  have hX' : RatFunc.X ∈ v.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]; exact hX.le
  refine ⟨v.valuationSubring, (algebraMap k (RatFunc k)).codRestrict v.valuationSubring hc,
    ⟨RatFunc.X, hX'⟩, ?_, rfl, ?_⟩
  · ext a; rfl
  · rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact ((Valuation.isEquiv_valuation_valuationSubring v).lt_one_iff_lt_one).1 hX

end GlobalTheory.FlagPush
