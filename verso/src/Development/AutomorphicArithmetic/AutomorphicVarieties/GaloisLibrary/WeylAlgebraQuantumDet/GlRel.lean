import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Bracket
open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Weyl.glRel :
    ∀ (n : ℕ) (Ξ : Pre n), Formalism.REAL.GlRel Ξ.E := by
  intro n Ξ a b c d
  have h := UpperTheory.V.Weyl.bracket n Ξ a b (Matrix.single c d 1)
  have h1 : Ξ.D (Matrix.single a b (1:ℂ) * Matrix.single c d 1) = if b = c then Ξ.E a d else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  have h2 : Ξ.D (Matrix.single c d (1:ℂ) * Matrix.single a b 1) = if d = a then Ξ.E c b else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  rw [map_sub, h1, h2] at h
  exact h
