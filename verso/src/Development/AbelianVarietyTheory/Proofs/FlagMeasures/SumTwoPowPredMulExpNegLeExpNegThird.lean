import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]`. Establish `h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n` using `pow_le_pow_left₀ (by positivity) (by linarith) n`.

Establish `h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n` using `by rw [mul_pow]; ring`. Establish `h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n` using `mul_le_mul_of_nonneg_left h2 h0`. Establish `h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1)) = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n` using `by ring`. Rewrite using `[h3, h5]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_two_pow_pred_mul_pow_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) (q : ℕ) :
    ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * r ^ J ≤ 2 * r * (1 - (1 / 2) ^ q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n := by rw [mul_pow]; ring
    have h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h2 h0
    have h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1))
        = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n := by ring
    rw [h3, h5]
    linarith

/- English proof (translation)
Introduce `q x hx`. Establish `hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J`. Introduce `J`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hr]`. Establish `h0 : 0 < Real.exp (-(x / 2))` using `Real.exp_pos _`. Establish `h1 : Real.exp (-(x / 2)) ≤ 1 / 4`. Rewrite using `[Real.exp_neg, one_div]`.

Apply `inv_anti₀ (by norm_num)` to reduce the goal to its premises. Use `Real.add_one_le_exp (x / 2)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_` and prove the remaining obligations. Establish `h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2))`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (2 : ℝ) ≤ Real.exp (x / 6)`. Use `Real.add_one_le_exp (x / 6)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : (0 : ℝ) ≤ (1 / 2) ^ q` using `by positivity`. Rewrite using `[h2]`. Use polynomial arithmetic with `[mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]`.
-/
theorem sum_two_pow_pred_mul_exp_neg_le :
    ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  intro q x hx
  have hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J := by
    intro J
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hr]
  have h0 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(x / 2)) ≤ 1 / 4 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp (x / 2)
    linarith
  refine (sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_
  have h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (2 : ℝ) ≤ Real.exp (x / 6) := by
    have := Real.add_one_le_exp (x / 6)
    linarith
  have h4 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [h2]
  nlinarith [mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]

end GlobalTheory
