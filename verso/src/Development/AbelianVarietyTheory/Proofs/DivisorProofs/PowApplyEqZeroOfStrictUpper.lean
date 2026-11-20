import Mathlib

namespace GlobalTheory.StrictUpperNilpotent

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `i j h`. Establish `hne : i ≠ j`.

Introduce and unpack `rfl`. Simplify using `at h`. Rewrite using `[pow_zero, Matrix.one_apply_ne hne]`. Consider the case `succ k ih`. Introduce `i j h`.

Rewrite using `[pow_succ, Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : (l : ℕ) < (i : ℕ) + k`. Rewrite using `[ih i l hl, zero_mul]`. Establish `hjl : j ≤ l`.

Rewrite using `[Fin.le_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hy l j hjl, mul_zero]`.
-/
theorem pow_apply_eq_zero_of_strictUpper {L : Type} [inst : Field L] {n : ℕ}
    {y : Matrix (Fin n) (Fin n) L} (hy : ∀ (i j : Fin n), j ≤ i → y i j = (0 : L)) :
    ∀ (k : ℕ) (i j : Fin n), (↑j : ℕ) < (↑i : ℕ) + k → (y ^ k) i j = (0 : L) := by
  intro k
  induction k with
  | zero =>
    intro i j h
    have hne : i ≠ j := by
      rintro rfl
      simp at h
    rw [pow_zero, Matrix.one_apply_ne hne]
  | succ k ih =>
    intro i j h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : (l : ℕ) < (i : ℕ) + k
    · rw [ih i l hl, zero_mul]
    · have hjl : j ≤ l := by
        rw [Fin.le_def]
        omega
      rw [hy l j hjl, mul_zero]

end GlobalTheory.StrictUpperNilpotent
