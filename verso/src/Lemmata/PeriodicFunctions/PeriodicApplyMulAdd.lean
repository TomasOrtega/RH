import Mathlib

open NumberField IsDedekindDomain Module

namespace Bl.PeriodicFunctions

variable {K : Type} [Field K]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Nat.mul_succ, show M * k + M + x = (M * k + x) + M by ring, hg, ih]`.
-/
private theorem periodic_apply_mul_add (M : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) (k x : ℕ) :
    g (M * k + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show M * k + M + x = (M * k + x) + M by ring, hg, ih]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih]`. Simplify using `only [periodic_apply_mul_add M g hg n]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem goal1 (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [periodic_apply_mul_add M g hg n]
    push_cast
    ring

end Bl.PeriodicFunctions
