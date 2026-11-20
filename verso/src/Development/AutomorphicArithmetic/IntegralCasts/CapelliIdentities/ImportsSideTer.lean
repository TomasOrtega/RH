import Mathlib

/- English proof (translation)
Introduce `n g g' D h1 h2 k`. Proceed by induction on `k with`. Consider the case `zero => simp [h1]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ih, pow_succ]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = g' * (D ^ k * D) * g := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]`.
-/
theorem UpperTheory.Reformulated.B.Yhd8.main :
    ∀ {n : ℕ} (g g' D : Matrix (Fin n) (Fin n) ℂ),
      g' * g = (1 : Matrix (Fin n) (Fin n) ℂ) →
        g * g' = (1 : Matrix (Fin n) (Fin n) ℂ) → ∀ (k : ℕ), (g' * D * g) ^ k = g' * D ^ k * g := by
  intro n g g' D h1 h2 k
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc g' * D ^ k * g * (g' * D * g) = g' * D ^ k * (g * g') * D * g := by
          simp only [Matrix.mul_assoc]
      _ = g' * (D ^ k * D) * g := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
