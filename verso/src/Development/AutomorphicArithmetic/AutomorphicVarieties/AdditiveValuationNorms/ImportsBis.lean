import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.PropA.mono :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a b : ℕ), a ∣ b →
      cokLen (g ^ a - 1) ≤ cokLen (g ^ b - 1) := by
  intro l _ X _ _ g a b hab
  apply cokLen_le_of_range_le
  obtain ⟨k, rfl⟩ := hab
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _
