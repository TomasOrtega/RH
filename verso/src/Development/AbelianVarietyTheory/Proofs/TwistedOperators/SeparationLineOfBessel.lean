import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)

namespace GlobalTheory.SepRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Distinguish the cases in `h0 : ∃ i, ∀ y, b i y = 0`. Take `⟨i, hi⟩` from `h0`. Use `⟨0, fun x => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `h i x`. Use `hc (x i)` as an intermediate fact.

Rewrite `this` using `[Function.update_eq_self, hi]`. Simplify using `[this]`. Use `push_neg at h0`. Use `choose x₀ hx₀ using h0`. Establish `key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) → β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i)`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]`. Consider the case `insert j s hj ih`. Introduce `x hx`.

Take `⟨c, hc⟩` from `h j x`. Establish `e1` using `hc (x j)`. Rewrite `e1` using `[Function.update_eq_self]`. Establish `e2` using `ih (Function.update x j (x₀ j)) fun i hi => by`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne e]; exact hx i (by simp [e, hi])`. Establish `e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i)` using `Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]`. Rewrite `e2` using `[hc, e3]`.

Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj, e1]`. Take the linear combination `b j (x j) * e2`. Establish `hn : ∏ i, b i (x₀ i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i`. Use `⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩` and prove the remaining obligations. Use `key Finset.univ x (by simp)` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Take the linear combination `this`.
-/
theorem mul_prod_of_separately {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (b : ∀ i, X i → ℂ) (β : (∀ i, X i) → ℂ)
    (h : ∀ i x, ∃ c : ℂ, ∀ y, β (Function.update x i y) = c * b i y) : ∃ l : ℂ, ∀ x, β x = (∏ i, b i (x i)) * l := by
  by_cases h0 : ∃ i, ∀ y, b i y = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun x => ?_⟩
    obtain ⟨c, hc⟩ := h i x
    have := hc (x i)
    rw [Function.update_eq_self, hi] at this
    simp [this]
  push_neg at h0
  choose x₀ hx₀ using h0
  have key : ∀ s : Finset ι, ∀ x, (∀ i, i ∉ s → x i = x₀ i) →
      β x * ∏ i ∈ s, b i (x₀ i) = β x₀ * ∏ i ∈ s, b i (x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x hx; rw [show x = x₀ from funext fun i => hx i (by simp)]
    | insert j s hj ih =>
      intro x hx
      obtain ⟨c, hc⟩ := h j x
      have e1 := hc (x j)
      rw [Function.update_eq_self] at e1
      have e2 := ih (Function.update x j (x₀ j)) fun i hi => by
        by_cases e : i = j
        · subst e; simp
        · rw [Function.update_of_ne e]; exact hx i (by simp [e, hi])
      have e3 : ∏ i ∈ s, b i (Function.update x j (x₀ j) i) = ∏ i ∈ s, b i (x i) :=
        Finset.prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hi hj)]
      rw [hc, e3] at e2
      rw [Finset.prod_insert hj, Finset.prod_insert hj, e1]
      linear_combination b j (x j) * e2
  have hn : ∏ i, b i (x₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hx₀ i
  refine ⟨β x₀ / ∏ i, b i (x₀ i), fun x => ?_⟩
  have := key Finset.univ x (by simp)
  field_simp
  linear_combination this

end GlobalTheory.SepRows

end
