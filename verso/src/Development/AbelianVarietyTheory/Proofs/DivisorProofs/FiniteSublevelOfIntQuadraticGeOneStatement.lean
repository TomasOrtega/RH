import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSublevelOfIntQuadraticGeOne
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteSublevelOfIntQuadraticGeOne.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.finite_sublevel_of_int_quadratic_ge_one : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (q : X → ℤ), (∀ a, q (-a) = q a) → (∀ a a' b, q (a + a' + b) + q a + q a' + q b = q (a + a') + q (a + b) + q (a' + b)) → (∀ a, a ≠ 0 → 1 ≤ q a) → ∀ N : ℤ, {a | q a ≤ N}.Finite := by
  first | exact @GlobalTheory.posquad_finite | exact GlobalTheory.posquad_finite | (intros; apply GlobalTheory.posquad_finite <;> assumption)
