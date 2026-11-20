import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

/- English proof (translation)
Introduce `n S v hS`. Use `⟨fun a => ?_, fun hne a => ?_⟩` and prove the remaining obligations. Unfold `poinWt split_ifs with ha`. Use `⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩` and prove the remaining obligations. Break down `(norm_nonneg (v a)).eq_or_lt with h0 | hpos` into its components or cases.

Rewrite using `[← h0]`. Simplify using the standard rewrite rules. Establish `h1 : ‖v a‖ ≤ 1` using `(hS a ha).trans (by norm_num)`. Use `Real.abs_log_mul_self_lt _ hpos h1` as an intermediate fact. Rewrite `this` using `[abs_mul, abs_of_pos hpos]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨zero_le_one, le_rfl⟩`. Unfold `poinWt split_ifs with ha`. Establish `hpos : 0 < ‖v a‖` using `norm_pos_iff.mpr (hne a ha)`. Establish `hlt : ‖v a‖ < 1` using `(hS a ha).trans_lt (by norm_num)`.

Establish `hlog : Real.log ‖v a‖ < 0` using `Real.log_neg hpos hlt`. Conclude with `mul_pos hpos (abs_pos.mpr hlog.ne)`. Conclude with `zero_lt_one`.
-/
theorem poinWt_mem_Icc_and_pos : ∀ {n : ℕ} (S : Finset (Fin n)) (v : V n), (∀ a ∈ S, ‖v a‖ ≤ 1 / 2) →
    (∀ a, 0 ≤ poinWt S v a ∧ poinWt S v a ≤ 1) ∧ ((∀ a ∈ S, v a ≠ 0) → ∀ a, 0 < poinWt S v a) := by
  intro n S v hS
  refine ⟨fun a => ?_, fun hne a => ?_⟩
  · unfold poinWt
    split_ifs with ha
    · refine ⟨mul_nonneg (norm_nonneg _) (abs_nonneg _), ?_⟩
      rcases (norm_nonneg (v a)).eq_or_lt with h0 | hpos
      · rw [← h0]; simp
      · have h1 : ‖v a‖ ≤ 1 := (hS a ha).trans (by norm_num)
        have := Real.abs_log_mul_self_lt _ hpos h1
        rw [abs_mul, abs_of_pos hpos] at this
        linarith
    · exact ⟨zero_le_one, le_rfl⟩
  · unfold poinWt
    split_ifs with ha
    · have hpos : 0 < ‖v a‖ := norm_pos_iff.mpr (hne a ha)
      have hlt : ‖v a‖ < 1 := (hS a ha).trans_lt (by norm_num)
      have hlog : Real.log ‖v a‖ < 0 := Real.log_neg hpos hlt
      exact mul_pos hpos (abs_pos.mpr hlog.ne)
    · exact zero_lt_one

end GlobalTheory.GoodTop
