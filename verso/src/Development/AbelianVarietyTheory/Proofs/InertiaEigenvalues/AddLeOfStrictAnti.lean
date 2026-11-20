import Mathlib

namespace GlobalTheory.StrictAntiAddLe

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem add_le_of_strictAnti : ∀ {m : ℕ} {s : Fin m → ℕ}, StrictAnti s →
    ∀ (k : ℕ) (i j : Fin m), (↑j : ℕ) = (↑i : ℕ) + k → s j + k ≤ s i := by
  intro m s hs k
  induction k with
  | zero =>
    intro i j h
    have hij : j = i := Fin.ext (by simpa using h)
    subst hij
    simp
  | succ k ih =>
    intro i j h
    have hj := j.isLt
    have hlt : (i : ℕ) + k < m := by omega
    have h1 := ih i ⟨(i : ℕ) + k, hlt⟩ rfl
    have h2 : s j < s ⟨(i : ℕ) + k, hlt⟩ := by
      apply hs
      rw [Fin.lt_def]
      show (i : ℕ) + k < (j : ℕ)
      omega
    omega

end GlobalTheory.StrictAntiAddLe
