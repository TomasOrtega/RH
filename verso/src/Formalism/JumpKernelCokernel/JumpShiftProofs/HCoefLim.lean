import Formalism.JumpKernelCokernel.Statement

noncomputable section

namespace Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

def P (s : ℝ) : ℝ := 25 + 57 * s + 40 * s ^ 2 + 8 * s ^ 3

/- English proof (translation)
Establish `h1 : x - 1 ≠ 0` using `by linarith`. Establish `h0 : x ≠ 0` using `by linarith`. Unfold `Formalism.KernelCokernelLengths.hCoef P`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hCoef_eq (x : ℝ) (hx : 1 < x) : Formalism.KernelCokernelLengths.hCoef x = P (1 / (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  unfold Formalism.KernelCokernelLengths.hCoef P
  field_simp
  ring

/- English proof (translation)
Unfold `P`. Establish `hs : 0 ≤ s` using `le_trans ht hts`. Use polynomial arithmetic with `[mul_le_mul hts hts ht hs, pow_le_pow_left₀ ht hts 3, pow_le_pow_left₀ ht hts 2]`.
-/
lemma P_mono {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) : P t ≤ P s := by
  unfold P
  have hs : 0 ≤ s := le_trans ht hts
  nlinarith [mul_le_mul hts hts ht hs, pow_le_pow_left₀ ht hts 3, pow_le_pow_left₀ ht hts 2]

/- English proof (translation)
Unfold `P`. Use polynomial arithmetic with `[pow_nonneg hs 2, pow_nonneg hs 3]`.
-/
lemma P_ge {s : ℝ} (hs : 0 ≤ s) : 25 ≤ P s := by
  unfold P
  nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]

end Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

open Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas in
/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx y hy hxy`. Simplify using `only [Set.mem_Ici] at hx hy`. Rewrite using `[hCoef_eq x (by linarith), hCoef_eq y (by linarith)]`. Apply `P_mono` to reduce the goal to its premises.

Establish `: 0 < y - 1` using `by linarith`. Check the signs of the components of the expression. Conclude with `one_div_le_one_div_of_le (by linarith) (by linarith)`. Introduce `x hx`. Rewrite using `[hCoef_eq x (by linarith)]`.

Apply `P_ge` to reduce the goal to its premises. Establish `: 0 < x - 1` using `by linarith`. Check the signs of the components of the expression. Establish `hs : Filter.Tendsto (fun x : ℝ => 1 / (x - 1)) Filter.atTop (nhds 0)`. Establish `h` using `tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)`.

Use `h.congr ?_` and prove the remaining obligations. Introduce `x`. Simplify using `[sub_eq_add_neg]`. Establish `hP : Continuous P` using `by unfold P; fun_prop`. Establish `h25 : P 0 = 25` using `by unfold P; norm_num`.

Establish `hlim : Filter.Tendsto (fun x : ℝ => P (1 / (x - 1))) Filter.atTop (nhds 25)`. Rewrite using `[← h25]`. Conclude with `(hP.tendsto 0).comp hs`. Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx`.

Conclude with `(hCoef_eq x hx).symm`.
-/
theorem Formalism.KernelCokernelLengths.coefficient_height_limit : Formalism.KernelCokernelLengths.HCoefLim := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    rw [hCoef_eq x (by linarith), hCoef_eq y (by linarith)]
    apply P_mono
    · have : 0 < y - 1 := by linarith
      positivity
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro x hx
    rw [hCoef_eq x (by linarith)]
    apply P_ge
    have : 0 < x - 1 := by linarith
    positivity
  · have hs : Filter.Tendsto (fun x : ℝ => 1 / (x - 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)
      refine h.congr ?_
      intro x
      simp [sub_eq_add_neg]
    have hP : Continuous P := by unfold P; fun_prop
    have h25 : P 0 = 25 := by unfold P; norm_num
    have hlim : Filter.Tendsto (fun x : ℝ => P (1 / (x - 1))) Filter.atTop (nhds 25) := by
      rw [← h25]; exact (hP.tendsto 0).comp hs
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hCoef_eq x hx).symm
