import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MulLogEqNegLogMul
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FMulLogEqNegLogMul.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.mul_log_eq_neg_log_mul' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x x' H H' : Matrix ι ι ℂ), IsLog H (xᴴ * x) → IsLog H' (x'ᴴ * x') → x' * x = 1 → x * H = -(H' * x) := by
  first | exact @GlobalTheory.ClassFin.mul_log_eq_neg_log_mul | exact GlobalTheory.ClassFin.mul_log_eq_neg_log_mul | (intros; apply GlobalTheory.ClassFin.mul_log_eq_neg_log_mul <;> assumption)
