import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOne
import Mathlib
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPosDefExistsConjTransposeMulMulEqOne.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  first | exact @GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | exact GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | (intros; apply GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one <;> assumption)
