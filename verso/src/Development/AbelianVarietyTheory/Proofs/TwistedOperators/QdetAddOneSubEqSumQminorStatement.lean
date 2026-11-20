import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetAddOneSubEqSumQminor
import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.qdet_add_one_sub_eq_sum_qminor` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FQdetAddOneSubEqSumQminor.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.qdet_add_one_sub_eq_sum_qminor' : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  first | exact @GlobalTheory.qdet_add_one_sub_eq_sum_qminor | exact GlobalTheory.qdet_add_one_sub_eq_sum_qminor | (intros; apply GlobalTheory.qdet_add_one_sub_eq_sum_qminor <;> assumption)
