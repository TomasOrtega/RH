import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCongruenceLiftLieElement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodRing
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CayleyUnit.cayley_unit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryCongruenceLiftLieElement.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.unitary_congruence_lift_lie_element : ∀ {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (τ : R →+* R) (H X : Matrix n n R) (p w : R) (k : ℕ), (∀ a, τ (τ a) = a) → τ p = p → w + τ w = 1 → (∀ s, IsUnit (1 + p * s)) → 1 ≤ k → Formalism.UG.cT τ X * H + H * X = 0 → ∃ g X' D : Matrix n n R, Formalism.UG.cT τ g * H * g = H ∧ g = 1 + p ^ k • X' ∧ X' = X + p • D := by
  first | exact @GlobalTheory.CayleyUnit.cayley_unit | exact GlobalTheory.CayleyUnit.cayley_unit | (intros; apply GlobalTheory.CayleyUnit.cayley_unit <;> assumption)
