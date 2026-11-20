import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitsFinitelyManyNorms
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.units_fixed_eq_mul_mul_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFixedUnitsFinitelyManyNorms.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.fixed_units_finitely_many_norms : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  first | exact @GlobalTheory.units_fixed_eq_mul_mul_conj | exact GlobalTheory.units_fixed_eq_mul_mul_conj | (intros; apply GlobalTheory.units_fixed_eq_mul_mul_conj <;> assumption)
