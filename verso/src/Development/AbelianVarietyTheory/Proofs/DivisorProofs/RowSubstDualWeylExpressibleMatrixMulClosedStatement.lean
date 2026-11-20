import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubstDualWeylExpressibleMatrixMulClosed
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rowSubstDualWeylExpressible_matrix_mul_closed : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ) (R : Type) [CommRing R] [Algebra O R] (Y Y' : Matrix (Fin N) (Fin N) R), Expr O N ν R Y → Expr O N ν R Y' → Expr O N ν R (Y * Y') := by
  first | exact @GlobalTheory.GenCoef.expr_mul | exact GlobalTheory.GenCoef.expr_mul | (intros; apply GlobalTheory.GenCoef.expr_mul <;> assumption)
