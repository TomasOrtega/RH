import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicValNatLogEqLog
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumPadicValNatLogEqLog.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.sum_padicValNat_log_eq_log : ∀ m : ℕ, m ≠ 0 → (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0).Finite ∧ ∑ᶠ p : ℕ, (if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) = Real.log m := by
  first | exact @GlobalTheory.finsum_padicValNat_mul_log_eq_log | exact GlobalTheory.finsum_padicValNat_mul_log_eq_log | (intros; apply GlobalTheory.finsum_padicValNat_mul_log_eq_log <;> assumption)
