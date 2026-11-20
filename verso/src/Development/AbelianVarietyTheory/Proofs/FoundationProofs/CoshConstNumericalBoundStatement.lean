import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshConstNumericalBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CartanInt.cosh_const_numerical_bound` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCoshConstNumericalBound.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.cosh_constant_le_exp_three_mul_sq_mul_log : ∀ (p q : ℕ), (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) * (2 ^ (2 * (p + q) * min p q) * (2 * Real.pi / (2 / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q)) ≤ Real.exp (3 * ((p + q : ℕ) : ℝ) ^ 2 * Real.log (((p + q : ℕ) : ℝ) + 2)) := by
  first | exact @GlobalTheory.CartanInt.cosh_const_numerical_bound | exact GlobalTheory.CartanInt.cosh_const_numerical_bound | (intros; apply GlobalTheory.CartanInt.cosh_const_numerical_bound <;> assumption)
