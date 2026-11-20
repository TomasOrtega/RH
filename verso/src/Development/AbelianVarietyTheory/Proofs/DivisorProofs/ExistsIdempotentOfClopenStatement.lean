import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIdempotentOfClopen.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_idempotent_of_clopen : ∀ (X : Scheme.{0}) (U : Set X), IsClopen U → ∃ e : Γ(X, ⊤), e * e = e ∧ ((X.basicOpen e : X.Opens) : Set X) = U := by
  first | exact @GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | exact GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen | (intros; apply GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen <;> assumption)
