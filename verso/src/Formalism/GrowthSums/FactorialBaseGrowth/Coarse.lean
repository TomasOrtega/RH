import Formalism.GrowthSums.StatementA

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `h1 : m + (k + 1) = (m + k) + 1` using `by omega`. Rewrite using `[h1, Nat.factorial_succ (m + k), Nat.factorial_succ k, Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]`.

Use `push_cast`. Rewrite using `[ih]`. Establish `hk : (k : ℚ) + 1 ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factorial_add_prod (m k : ℕ) :
    (((m + k).factorial : ℕ) : ℚ) =
      (m.factorial : ℚ) * (k.factorial : ℚ) * ∏ y ∈ Ico 1 (k + 1), (1 + (m : ℚ) / y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, Nat.factorial_succ (m + k), Nat.factorial_succ k,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    rw [ih]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring

/- English proof (translation)
Establish `hPq : (P : ℚ) ≠ 0` using `by exact_mod_cast (show P ≠ 0 by omega)`. Establish `key` using `factorial_add_prod (P * n) P`. Move the coercions through the operations in `at key`. Rewrite `key` using `[Finset.prod_Ico_succ_top hP, mul_div_cancel_left₀ _ hPq]`. Establish `hfP : (P.factorial : ℚ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero P`.

Establish `hfn : (n.factorial : ℚ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero n`. Establish `hn1 : (n : ℚ) + 1 ≠ 0` using `by positivity`. Unfold `coarseUnit`. Rewrite using `[show P * (n + 1) = P * n + P by ring, key, Nat.factorial_succ n]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coarseUnit_succ (P n : ℕ) (hP : 1 ≤ P) :
    coarseUnit P (n + 1) = coarseUnit P n * ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * n / y) := by
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  have key := factorial_add_prod (P * n) P
  push_cast at key
  rw [Finset.prod_Ico_succ_top hP, mul_div_cancel_left₀ _ hPq] at key
  have hfP : (P.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero P
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  unfold coarseUnit
  rw [show P * (n + 1) = P * n + P by ring, key, Nat.factorial_succ n]
  push_cast
  field_simp
  ring

/- English proof (translation)
Introduce `P n hP`. Proceed by induction on `n with`. Consider the case `zero => simp [coarseUnit]`. Consider the case `succ n ih => rw [coarseUnit_succ P n hP, ih, Finset.prod_range_succ]`.
-/
theorem blockFactorialQuotientProd : CoarseUnitProd := by
  intro P n hP
  induction n with
  | zero => simp [coarseUnit]
  | succ n ih => rw [coarseUnit_succ P n hP, ih, Finset.prod_range_succ]

end Formalism.GrowthSums
