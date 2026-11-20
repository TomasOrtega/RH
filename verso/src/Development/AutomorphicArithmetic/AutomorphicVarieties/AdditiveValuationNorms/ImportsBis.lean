import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Introduce `l _ X _ _ g a b hab`. Apply `cokLen_le_of_range_le` to reduce the goal to its premises. Take `⟨k, rfl⟩` from `hab`. Rewrite using `[pow_mul, ← mul_geom_sum]`. Conclude with `LinearMap.range_comp_le_range _ _`.
-/
theorem UpperTheory.V.PropA.mono :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a b : ℕ), a ∣ b →
      cokLen (g ^ a - 1) ≤ cokLen (g ^ b - 1) := by
  intro l _ X _ _ g a b hab
  apply cokLen_le_of_range_le
  obtain ⟨k, rfl⟩ := hab
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _
