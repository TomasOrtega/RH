import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Establish `h : Measurable fun p : ℝ × ℕ => g p.2 p.1` using `measurable_from_prod_countable_left fun k => hg k`. Conclude with `h.comp (measurable_id.prodMk Nat.measurable_floor)`.
-/
theorem measurable_Gchi_floor (g : ℕ → ℝ → ℂ) (hg : ∀ k, Measurable (g k)) :
    Measurable (fun y : ℝ => g ⌊y⌋₊ y) := by
  have h : Measurable fun p : ℝ × ℕ => g p.2 p.1 :=
    measurable_from_prod_countable_left fun k => hg k
  exact h.comp (measurable_id.prodMk Nat.measurable_floor)

/- English proof (translation)
Unfold `ramp`. Use `measurable_Gchi_floor (fun k y => ∑ n ∈ Finset.range (k + 1), (ArithmeticFunction.vonMangoldt n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) ?_` and prove the remaining obligations. Introduce `k`. Use `Finset.measurable_sum _ fun n _ => ?_` and prove the remaining obligations. Use `fun_prop`.
-/
theorem measurable_Gchi_ramp (f : ℕ → ℂ) : Measurable (ramp f) := by
  unfold ramp
  refine measurable_Gchi_floor
    (fun k y => ∑ n ∈ Finset.range (k + 1),
      (ArithmeticFunction.vonMangoldt n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)) ?_
  intro k
  refine Finset.measurable_sum _ fun n _ => ?_
  fun_prop

/- English proof (translation)
Unfold `Gchi`. Use `split_ifs`. Conclude with `((measurable_Gchi_ramp _).sub (by fun_prop)).add (by fun_prop)`. Conclude with `(measurable_Gchi_ramp _).add (by fun_prop)`.
-/
theorem measurable_Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Measurable (Gchi χ) := by
  unfold Gchi
  split_ifs
  · exact ((measurable_Gchi_ramp _).sub (by fun_prop)).add (by fun_prop)
  · exact (measurable_Gchi_ramp _).add (by fun_prop)

end Deduction

end
