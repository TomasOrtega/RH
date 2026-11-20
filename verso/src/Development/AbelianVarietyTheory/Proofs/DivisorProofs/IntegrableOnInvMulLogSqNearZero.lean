import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Unfold `ContinuousAt`. Simplify using `only [Real.log_zero, inv_zero]`. Use `Tendsto.mono_left (x := 𝓝[≠] (0:ℝ) ⊔ pure 0) ?_ (nhdsNE_sup_pure (0:ℝ)).ge` and prove the remaining obligations. Use `Tendsto.sup ?_ ?_` and prove the remaining obligations. Conclude with `tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero`.

Rewrite using `[tendsto_pure_left]`. Introduce `s hs`. Simplify using `using mem_of_mem_nhds hs`.
-/
theorem continuousAt_inv_log_zero : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) 0 := by
  unfold ContinuousAt
  simp only [Real.log_zero, inv_zero]
  refine Tendsto.mono_left (x := 𝓝[≠] (0:ℝ) ⊔ pure 0) ?_ (nhdsNE_sup_pure (0:ℝ)).ge
  refine Tendsto.sup ?_ ?_
  · exact tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero
  · rw [tendsto_pure_left]
    intro s hs
    simpa using mem_of_mem_nhds hs

/- English proof (translation)
Establish `hcont : ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Set.Icc 0 (1 / 2))`. Introduce `t ht`. Break down `eq_or_lt_of_le ht.1 with h | h` into its components or cases. Substitute `h` using the available equality. Conclude with `(continuousAt_inv_log_zero.neg).continuousWithinAt`.

Establish `hlog : Real.log t ≠ 0`. Establish `: Real.log t < 0` using `Real.log_neg h (by linarith [ht.2])`. Conclude with `this.ne`. Conclude with `((Real.continuousAt_log h.ne').inv₀ hlog).neg.continuousWithinAt`. Use `intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_` and prove the remaining obligations.

Introduce `t ht`. Establish `ht0 : 0 < t` using `ht.1`. Establish `hlogneg : Real.log t < 0` using `Real.log_neg ht0 (by linarith [ht.2])`. Establish `hlog : Real.log t ≠ 0` using `hlogneg.ne`. Establish `h1 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t` using `((Real.hasDerivAt_log ht0.ne').inv hlog).neg`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[abs_of_neg hlogneg]`. Clear the denominators using the available nonvanishing facts. Introduce `t ht`. Use `ht.1` as an intermediate fact.

Check the signs of the components of the expression.
-/
theorem integrableOn_inv_mul_log_sq :
    IntegrableOn (fun t : ℝ => t * (t * |Real.log t|)⁻¹ ^ 2) (Set.Ioc 0 (1 / 2)) := by
  have hcont : ContinuousOn (fun t : ℝ => -(Real.log t)⁻¹) (Set.Icc 0 (1 / 2)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      exact (continuousAt_inv_log_zero.neg).continuousWithinAt
    · have hlog : Real.log t ≠ 0 := by
        have : Real.log t < 0 := Real.log_neg h (by linarith [ht.2])
        exact this.ne
      exact ((Real.continuousAt_log h.ne').inv₀ hlog).neg.continuousWithinAt
  refine intervalIntegral.integrableOn_deriv_of_nonneg hcont ?_ ?_
  · intro t ht
    have ht0 : 0 < t := ht.1
    have hlogneg : Real.log t < 0 := Real.log_neg ht0 (by linarith [ht.2])
    have hlog : Real.log t ≠ 0 := hlogneg.ne
    have h1 : HasDerivAt (fun t => -(Real.log t)⁻¹) (-(-t⁻¹ / Real.log t ^ 2)) t :=
      ((Real.hasDerivAt_log ht0.ne').inv hlog).neg
    convert h1 using 1
    rw [abs_of_neg hlogneg]
    field_simp
  · intro t ht
    have := ht.1
    positivity

end GlobalTheory.GoodTop
