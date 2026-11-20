import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix

namespace GlobalTheory.BKReal

/- English proof (translation)
Proceed by induction on `p generalizing m with`. Consider the case `zero => simp`. Consider the case `succ p ih`. Rewrite using `[Function.iterate_succ_apply', coeff_derivative, ih, Nat.descFactorial_succ, show m + 1 + p = m + (p + 1) by omega, show m + (p + 1) - p = m + 1 by omega]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_iterate_derivative_descFactorial (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧) (m : ℕ) :
    coeff m ((⇑(derivative K))^[p] f) = ((m + p).descFactorial p : K) * coeff (m + p) f := by
  induction p generalizing m with
  | zero => simp
  | succ p ih =>
    rw [Function.iterate_succ_apply', coeff_derivative, ih, Nat.descFactorial_succ,
      show m + 1 + p = m + (p + 1) by omega, show m + (p + 1) - p = m + 1 by omega]
    push_cast
    ring

/- English proof (translation)
Introduce `K _ p f`. Use extensionality with `n`. Rewrite using `[coeff_descN, coeff_X_pow_mul']`. Use `split_ifs with h`. Rewrite using `[coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]`.

Rewrite using `[Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]`.
-/
theorem descN_eq_X_pow_mul_iterate_derivative :
    ∀ (K : Type) [NormedField K] (p : ℕ) (f : K⟦X⟧), descN K p f = X ^ p * (⇑(derivative K))^[p] f := by
  intro K _ p f
  ext n
  rw [coeff_descN, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_iterate_derivative_descFactorial, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, zero_mul]

end GlobalTheory.BKReal
