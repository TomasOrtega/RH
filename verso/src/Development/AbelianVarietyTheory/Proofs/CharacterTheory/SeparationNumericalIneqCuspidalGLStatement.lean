import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SeparationNumericalIneqCuspidalGL
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FCharacterTheory%2FSeparationNumericalIneqCuspidalGL.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.separation_numerical_ineq_cuspidalGL : ∀ q n : ℕ, 2 ≤ q → 0 < n → ¬ (q = 2 ∧ (n = 4 ∨ n = 6)) → (n - 1) ^ 2 + 4 * n ^ 2 * ∑ p ∈ n.primeFactors, (q ^ (n / p) - 2) < 2 * n * (q ^ n - 1) := by
  first | exact @GlobalTheory.CuspGL.sep_numerical_ineq | exact GlobalTheory.CuspGL.sep_numerical_ineq | (intros; apply GlobalTheory.CuspGL.sep_numerical_ineq <;> assumption)
