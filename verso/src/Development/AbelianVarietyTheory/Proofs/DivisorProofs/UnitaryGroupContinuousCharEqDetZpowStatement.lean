import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupContinuousCharEqDetZpow
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryChar.char_eq_det_zpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryGroupContinuousCharEqDetZpow.lean&line=133#L133)
-/
theorem _root_.GlobalTheory.T.unitaryGroup_continuous_char_eq_det_zpow : ∀ (n : ℕ) (c : Matrix.unitaryGroup (Fin n) ℂ →* Circle), Continuous c → ∃ m : ℤ, ∀ u : Matrix.unitaryGroup (Fin n) ℂ, ((c u : Circle) : ℂ) = (Matrix.det (u : Matrix (Fin n) (Fin n) ℂ)) ^ m := by
  first | exact @GlobalTheory.UnitaryChar.char_eq_det_zpow | exact GlobalTheory.UnitaryChar.char_eq_det_zpow | (intros; apply GlobalTheory.UnitaryChar.char_eq_det_zpow <;> assumption)
