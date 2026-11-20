import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.BoundConv

/- English proof (translation)
Use `set A := |C₅| with hA`. Use `set M' := |M| with hM'`. Establish `hA0 : 0 ≤ A` using `abs_nonneg _`. Establish `hM0 : 0 ≤ M'` using `abs_nonneg _`. Establish `hB1 : 1 ≤ (1 + M') ^ A` using `Real.one_le_rpow (by linarith) hA0`.

Establish `hE1 : 1 + M' ≤ Real.exp M'` using `by linarith [Real.add_one_le_exp M']`. Establish `hE1' : 1 ≤ Real.exp M'` using `Real.one_le_exp hM0`. Use `set K := A * (1 + M') ^ A * Real.exp M' with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hKA : A ≤ K`.

Establish `: A * 1 * 1 ≤ A * (1 + M') ^ A * Real.exp M'` using `mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1' (by norm_num) (by positivity)`. Simplify using `using this`. Establish `hKA' : A * (1 + M') ≤ K`. Establish `: A * 1 * (1 + M') ≤ A * (1 + M') ^ A * Real.exp M'` using `mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1 (by linarith) (by positivity)`. Simplify using `using this`.

Use `⟨K, hK0, ?_⟩` and prove the remaining obligations. Introduce `x y p d hx hy hxy`. Establish `he1 : 1 ≤ Real.exp 1` using `Real.one_le_exp (by norm_num)`. Establish `hy1 : 1 ≤ y` using `le_trans he1 hy`. Establish `hx1 : 1 ≤ x` using `le_trans he1 hx`.

Establish `hlogy : 1 ≤ Real.log y`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]; exact hy`. Establish `hlogx : 1 ≤ Real.log x`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]; exact hx`. Establish `hxle : x ≤ y + M'`.

Use `(abs_le.mp (le_trans hxy (le_abs_self M))).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hxle2 : x ≤ y * (1 + M')` using `by nlinarith`. Prove the components needed by the constructor for the conclusion. Introduce `hp1 hp2`.

Use `⟨?_, le_trans hp2 (le_trans (le_abs_self C₅) hKA)⟩` and prove the remaining obligations. Break down `le_or_gt C₅ 0 with hC | hC` into its components or cases. Establish `h1 : 0 ≤ -C₅ * Real.log x` using `mul_nonneg (by linarith) (by linarith)`. Establish `h2 : 0 ≤ K * Real.log y` using `mul_nonneg hK0 (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hAC : A = C₅` using `abs_of_pos hC`. Establish `hl1 : Real.log x ≤ Real.log (y * (1 + M'))` using `Real.log_le_log (by linarith) hxle2`. Rewrite `hl1` using `[Real.log_mul (by linarith) (by linarith)]`. Establish `hl2 : Real.log (1 + M') ≤ M'`. Use `Real.log_le_sub_one_of_pos (show 0 < 1 + M' by linarith); linarith` as an intermediate fact.

Establish `hl3 : Real.log x ≤ Real.log y * (1 + M')` using `by nlinarith`. Establish `hl4 : C₅ * Real.log x ≤ C₅ * (1 + M') * Real.log y`. Use `mul_le_mul_of_nonneg_left hl3 hC.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hl5 : C₅ * (1 + M') * Real.log y ≤ K * Real.log y` using `mul_le_mul_of_nonneg_right (by rw [← hAC]; exact hKA') (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `hd`. Establish `h1 : x ^ A ≤ (y * (1 + M')) ^ A` using `Real.rpow_le_rpow (by linarith) hxle2 hA0`. Rewrite `h1` using `[Real.mul_rpow (by linarith) (by linarith)]`. Establish `h2 : Real.exp (x / 2) ≤ Real.exp (y / 2) * Real.exp M'`.

Rewrite using `[← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)`. Establish `h3 : y ^ A ≤ y ^ K` using `Real.rpow_le_rpow_of_exponent_le hy1 hKA`. Establish `hxA : 0 ≤ x ^ A` using `Real.rpow_nonneg (by linarith) _`. Establish `hyK : 0 ≤ y ^ K` using `Real.rpow_nonneg (by linarith) _`. Establish `hB0 : 0 ≤ (1 + M') ^ A` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (mul_le_mul_of_nonneg_left h1 hA0) h2 (Real.exp_pos _).le` to reduce the goal to its premises. Check the signs of the components of the expression. Use `_ ≤ A * (y ^ K * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by`. Apply `mul_le_mul_of_nonneg_right _ (by positivity)` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hA0`. Use `_ = K * y ^ K * Real.exp (y / 2) := by rw [hK]; ring`.
-/
theorem bound_conv_local (C₅ M : ℝ) : ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) := by
  set A := |C₅| with hA
  set M' := |M| with hM'
  have hA0 : 0 ≤ A := abs_nonneg _
  have hM0 : 0 ≤ M' := abs_nonneg _
  have hB1 : 1 ≤ (1 + M') ^ A := Real.one_le_rpow (by linarith) hA0
  have hE1 : 1 + M' ≤ Real.exp M' := by linarith [Real.add_one_le_exp M']
  have hE1' : 1 ≤ Real.exp M' := Real.one_le_exp hM0
  set K := A * (1 + M') ^ A * Real.exp M' with hK
  have hK0 : 0 ≤ K := by positivity
  have hKA : A ≤ K := by
    have : A * 1 * 1 ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1' (by norm_num) (by positivity)
    simpa using this
  have hKA' : A * (1 + M') ≤ K := by
    have : A * 1 * (1 + M') ≤ A * (1 + M') ^ A * Real.exp M' :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB1 hA0) hE1 (by linarith) (by positivity)
    simpa using this
  refine ⟨K, hK0, ?_⟩
  intro x y p d hx hy hxy
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hy1 : 1 ≤ y := le_trans he1 hy
  have hx1 : 1 ≤ x := le_trans he1 hx
  have hlogy : 1 ≤ Real.log y := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hy
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; exact hx
  have hxle : x ≤ y + M' := by
    have := (abs_le.mp (le_trans hxy (le_abs_self M))).2
    linarith
  have hxle2 : x ≤ y * (1 + M') := by nlinarith
  constructor
  · intro hp1 hp2
    refine ⟨?_, le_trans hp2 (le_trans (le_abs_self C₅) hKA)⟩
    rcases le_or_gt C₅ 0 with hC | hC
    · have h1 : 0 ≤ -C₅ * Real.log x := mul_nonneg (by linarith) (by linarith)
      have h2 : 0 ≤ K * Real.log y := mul_nonneg hK0 (by linarith)
      linarith
    · have hAC : A = C₅ := abs_of_pos hC
      have hl1 : Real.log x ≤ Real.log (y * (1 + M')) := Real.log_le_log (by linarith) hxle2
      rw [Real.log_mul (by linarith) (by linarith)] at hl1
      have hl2 : Real.log (1 + M') ≤ M' := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + M' by linarith); linarith
      have hl3 : Real.log x ≤ Real.log y * (1 + M') := by nlinarith
      have hl4 : C₅ * Real.log x ≤ C₅ * (1 + M') * Real.log y := by
        have := mul_le_mul_of_nonneg_left hl3 hC.le; linarith
      have hl5 : C₅ * (1 + M') * Real.log y ≤ K * Real.log y :=
        mul_le_mul_of_nonneg_right (by rw [← hAC]; exact hKA') (by linarith)
      linarith
  · intro hd
    have h1 : x ^ A ≤ (y * (1 + M')) ^ A := Real.rpow_le_rpow (by linarith) hxle2 hA0
    rw [Real.mul_rpow (by linarith) (by linarith)] at h1
    have h2 : Real.exp (x / 2) ≤ Real.exp (y / 2) * Real.exp M' := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have h3 : y ^ A ≤ y ^ K := Real.rpow_le_rpow_of_exponent_le hy1 hKA
    have hxA : 0 ≤ x ^ A := Real.rpow_nonneg (by linarith) _
    have hyK : 0 ≤ y ^ K := Real.rpow_nonneg (by linarith) _
    have hB0 : 0 ≤ (1 + M') ^ A := by linarith
    calc d ≤ A * x ^ A * Real.exp (x / 2) := hd
      _ ≤ A * (y ^ A * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left h1 hA0) h2 (Real.exp_pos _).le
          positivity
      _ ≤ A * (y ^ K * (1 + M') ^ A) * (Real.exp (y / 2) * Real.exp M') := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hB0) hA0
      _ = K * y ^ K * Real.exp (y / 2) := by rw [hK]; ring

/- English proof (translation)
The claim follows from `bound_conv_local`.
-/
theorem bound_conv : ∀ (C₅ M : ℝ), ∃ C₅' : ℝ, 0 ≤ C₅' ∧ ∀ (rw rl p d : ℝ), Real.exp 1 ≤ rw → Real.exp 1 ≤ rl → |rw - rl| ≤ M → (-C₅ * Real.log rw ≤ p → p ≤ C₅ → -C₅' * Real.log rl ≤ p ∧ p ≤ C₅') ∧ (d ≤ |C₅| * rw ^ |C₅| * Real.exp (rw / 2) → d ≤ C₅' * rl ^ C₅' * Real.exp (rl / 2)) :=
  bound_conv_local

end GlobalTheory.CompanionTheory.Metric.BoundConv
