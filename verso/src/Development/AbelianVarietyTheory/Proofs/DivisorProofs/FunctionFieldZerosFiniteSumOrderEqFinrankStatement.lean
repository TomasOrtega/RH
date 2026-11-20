import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldZerosFiniteSumOrderEqFinrank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.zeros_finite_sum_eq_degree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFunctionFieldZerosFiniteSumOrderEqFinrank.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.functionField_zeros_finite_sum_order_eq_finrank : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ x : F, Transcendental k x → {v : Place k F | v.1 x < 1}.Finite ∧ ∑ᶠ v ∈ {v : Place k F | v.1 x < 1}, ord v x = Module.finrank k⟮x⟯ F := by
  first | exact @GlobalTheory.Nef.zeros_finite_sum_eq_degree | exact GlobalTheory.Nef.zeros_finite_sum_eq_degree | (intros; apply GlobalTheory.Nef.zeros_finite_sum_eq_degree <;> assumption)
