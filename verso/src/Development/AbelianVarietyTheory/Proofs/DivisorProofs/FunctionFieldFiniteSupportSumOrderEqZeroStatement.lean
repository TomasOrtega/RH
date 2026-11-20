import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFunctionFieldFiniteSupportSumOrderEqZero.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.functionField_finite_support_sum_order_eq_zero : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, x ≠ 0 → {v : Place k F | v.1 x ≠ 1}.Finite ∧ ∑ᶠ v : Place k F, ord v x = 0 := by
  first | exact @GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | exact GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero | (intros; apply GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero <;> assumption)
