import Mathlib

namespace GlobalTheory.PeriodicSumShift

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i`. Simplify using the standard rewrite rules. Consider the case `succ k ih => intro i`.

Rewrite using `[Nat.mul_succ, add_assoc, ih, h]`.
-/
theorem periodic_shift {K : Type} (g : ℕ → K) (N : ℕ) (h : ∀ i, g (N + i) = g i) :
    ∀ k i, g (N * k + i) = g i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih => intro i; rw [Nat.mul_succ, add_assoc, ih, h]

/- English proof (translation)
Introduce `K _ g N h k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Nat.mul_succ, Finset.sum_range_add, ih]`.

Repeatedly rewrite using `[periodic_shift g N h k]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_range_mul_of_periodic : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [periodic_shift g N h k]
    push_cast; ring

end GlobalTheory.PeriodicSumShift
