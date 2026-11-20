import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosDefConjTransposeMulSelfEqExpPolynomial
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPosDefConjTransposeMulSelfEqExpPolynomial.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_exp_eq_conjTranspose_mul_poly : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ), IsUnit g → ∃ (L : Matrix (Fin n) (Fin n) ℂ) (p : Polynomial ℂ), Lᴴ = L ∧ NormedSpace.exp L = gᴴ * g ∧ L = Polynomial.aeval (gᴴ * g) p := by
  first | exact @GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | exact GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial | (intros; apply GlobalTheory.posDef_conjTranspose_mul_self_eq_exp_polynomial <;> assumption)
