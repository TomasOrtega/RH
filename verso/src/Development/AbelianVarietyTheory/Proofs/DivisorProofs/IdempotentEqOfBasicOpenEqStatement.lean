import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentEqOfBasicOpenEq
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdempotentEqOfBasicOpenEq.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.idempotent_eq_of_basicOpen_eq' : ∀ (X : Scheme.{0}) (e e' : Γ(X, ⊤)), e * e = e → e' * e' = e' → X.basicOpen e = X.basicOpen e' → e = e' := by
  first | exact @GlobalTheory.idempotent_eq_of_basicOpen_eq | exact GlobalTheory.idempotent_eq_of_basicOpen_eq | (intros; apply GlobalTheory.idempotent_eq_of_basicOpen_eq <;> assumption)
