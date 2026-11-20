import Mathlib

namespace YhaHelp
open MeasureTheory Set Real

/- English proof (translation)
Rewrite using `[integrable_indicator_iff measurableSet_Ici]`. Conclude with `(exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by`. Simplify using `only [mem_Ici, mem_Ioi] at *`. Use the proof step `linarith)`.
-/
private lemma F_int {c : ℝ} (hc : 0 < c) :
    Integrable ((Ici (0:ℝ)).indicator (fun x : ℝ => exp (-c * x))) := by
  rw [integrable_indicator_iff measurableSet_Ici]
  exact (exp_neg_integrableOn_Ioi (-1) hc).mono_set (fun x hx => by
    simp only [mem_Ici, mem_Ioi] at *; linarith)

end YhaHelp

/- English proof (translation)
Introduce `c hc`. Establish `hF` using `YhaHelp.F_int hc`. Establish `hG` using `hF.comp_neg`. Use `(hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`.

Simplify using `only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]`. Break down `le_or_gt 0 x with h | h` into its components or cases. Rewrite using `[abs_of_nonneg h, if_pos h] split_ifs`. Combine the linear relations using `[Real.exp_pos (-c * -x)]`. Simplify using the standard rewrite rules.

Rewrite using `[abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.Yha4.main :
    ∀ {c : ℝ}, (0 : ℝ) < c → MeasureTheory.Integrable (fun (x : ℝ) ↦ Real.exp (-c * |x|)) MeasureTheory.MeasureSpace.volume := by
  intro c hc
  have hF := YhaHelp.F_int hc
  have hG := hF.comp_neg
  refine (hF.add hG).mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [Pi.add_apply, Set.indicator, Set.mem_Ici, Left.nonneg_neg_iff]
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, if_pos h]
    split_ifs
    · linarith [Real.exp_pos (-c * -x)]
    · simp
  · rw [abs_of_neg h, if_neg (not_le.mpr h), if_pos h.le]
    simp
