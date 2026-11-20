import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBound
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPosSemidefQuadraticAdjointPairBound.lean&line=105#L105)
-/
theorem _root_.GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y := by
  first | exact @GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | exact GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | (intros; apply GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound <;> assumption)
