import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

variable {n : ℕ}

/- English proof (translation)
Apply the tactic sequence `by_cases h : i = b <;> simp [tensVd, h]`.
-/
theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

/- English proof (translation)
Simplify using `[eeVd]`.
-/
theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun a => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]`. Simplify using `only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]`. Distinguish the cases in `h : a = d`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Simplify using `[h, Ne.symm h]`.
-/
theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_
  simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

/- English proof (translation)
Introduce `_ X z a b _ hx` and use `Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx`.
-/
theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
