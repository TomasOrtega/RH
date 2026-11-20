import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HPolyAddTwo

set_option autoImplicit false

open MeasureTheory MvPolynomial GlobalTheory.FibLine

namespace GlobalTheory.FibLine

/- English proof (translation)
Proceed by induction on `k using Nat.twoStepInduction with`. Consider the case `zero => simp [hPoly_zero]`. Consider the case `one => simp [hPoly_one]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `more k h0 h1`.

Rewrite using `[hPoly_add_two]`. Simplify using `only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Take the linear combination `(a + b) * h1 - (a * b) * h0`.
-/
theorem sub_mul_eval_hPoly (a b : ℂ) (k : ℕ) :
    (a - b) * MvPolynomial.eval ![a + b, a * b] (hPoly k) = a ^ (k + 1) - b ^ (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination (a + b) * h1 - (a * b) * h0

/- English proof (translation)
Proceed by induction on `k using Nat.twoStepInduction with`. Consider the case `zero => simp [hPoly_zero]`. Consider the case `one => simp [hPoly_one]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `more k h0 h1`.

Rewrite using `[hPoly_add_two]`. Simplify using `only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Rewrite using `[h0, h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_hPoly_diag (a : ℂ) (k : ℕ) :
    MvPolynomial.eval ![a + a, a * a] (hPoly k) = ((k : ℂ) + 1) * a ^ k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [hPoly_zero]
  | one => simp [hPoly_one]; ring
  | more k h0 h1 =>
    rw [hPoly_add_two]
    simp only [map_sub, map_mul, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [h0, h1]
    push_cast
    ring

/- English proof (translation)
Establish `hk : ((k : ℂ) + 1) ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero k`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `: ∀ t : ℝ, ((t : ℂ) * a + (1 - (t : ℂ)) * a) ^ k = a ^ k` using `fun t => by ring`. Simplify using `only [this]`.

Rewrite using `[eval_hPoly_diag]`. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Establish `hab' : a - b ≠ 0` using `sub_ne_zero.mpr hab`. Establish `hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ (k + 1) / (((k : ℂ) + 1) * (a - b))) (((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) t`.

Introduce `t _`. Establish `h1 : HasDerivAt (fun z : ℂ => z * a + (1 - z) * b) (a - b) (t : ℂ)`. Use `((hasDerivAt_id (t : ℂ)).mul_const a).add (((hasDerivAt_id (t : ℂ)).const_sub 1).mul_const b)` as an intermediate fact. Conclude with `this.congr_deriv (by ring)`. Establish `h2` using `((h1.pow (k + 1)).div_const (((k : ℂ) + 1) * (a - b))).comp_ofReal`.

Use `h2.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[intervalIntegral.integral_eq_sub_of_hasDerivAt hder (Continuous.intervalIntegrable (by fun_prop) _ _)]`.

Establish `h` using `sub_mul_eval_hPoly a b k`. Simplify using `only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero]`. Rewrite using `[← sub_div, ← h]`. Clear the denominators using the available nonvanishing facts.
-/
theorem integral_affine_pow_eq_hPoly (k : ℕ) (a b : ℂ) :
    ∫ t in (0 : ℝ)..1, ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k
      = MvPolynomial.eval ![a + b, a * b] (hPoly k) / ((k : ℂ) + 1) := by
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  by_cases hab : a = b
  · subst hab
    have : ∀ t : ℝ, ((t : ℂ) * a + (1 - (t : ℂ)) * a) ^ k = a ^ k := fun t => by ring
    simp only [this]
    rw [eval_hPoly_diag]
    simp
    field_simp
  · have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hder : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
        (fun t : ℝ => ((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ (k + 1) / (((k : ℂ) + 1) * (a - b)))
        (((t : ℂ) * a + (1 - (t : ℂ)) * b) ^ k) t := by
      intro t _
      have h1 : HasDerivAt (fun z : ℂ => z * a + (1 - z) * b) (a - b) (t : ℂ) := by
        have := ((hasDerivAt_id (t : ℂ)).mul_const a).add
          (((hasDerivAt_id (t : ℂ)).const_sub 1).mul_const b)
        exact this.congr_deriv (by ring)
      have h2 := ((h1.pow (k + 1)).div_const (((k : ℂ) + 1) * (a - b))).comp_ofReal
      refine h2.congr_deriv ?_
      simp only [Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have h := sub_mul_eval_hPoly a b k
    simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero]
    rw [← sub_div, ← h]
    field_simp

end GlobalTheory.FibLine
