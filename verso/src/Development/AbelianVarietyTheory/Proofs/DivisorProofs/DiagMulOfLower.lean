import Mathlib

namespace GlobalTheory.DiagonalTimesLowerTriangular

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem diag_mul_of_lower {K : Type} [CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}
    (ha : ∀ (i j : Fin s), i < j → a i j = (0 : K))
    (hb : ∀ (i j : Fin s), i < j → b i j = (0 : K)) :
    ∀ (i : Fin s), (a * b) i i = a i i * b i i := by
  intro i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hb k i h, mul_zero]
    · rw [ha i k h, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem main : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i :=
  fun ha hb => diag_mul_of_lower ha hb

end GlobalTheory.DiagonalTimesLowerTriangular
