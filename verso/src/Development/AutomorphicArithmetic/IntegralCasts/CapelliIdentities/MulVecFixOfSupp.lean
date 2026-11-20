import Mathlib

/- English proof (translation)
Introduce `m y v h`. Establish `key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hj : v j = 0`. Rewrite using `[hj, mul_zero, mul_zero]`. Rewrite using `[h j hj i, Matrix.one_apply]`. Rewrite using `[key, Matrix.one_mulVec]`.
-/
theorem UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by
  intro m y v h
  have key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : v j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj i, Matrix.one_apply]
  rw [key, Matrix.one_mulVec]
