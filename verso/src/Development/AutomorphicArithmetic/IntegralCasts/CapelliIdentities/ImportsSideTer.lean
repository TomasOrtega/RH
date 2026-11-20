import Mathlib

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
