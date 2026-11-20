import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLift
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPadicIntExistsLevelNotDvdMulLift.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift : ∀ (l : ℕ) [Fact l.Prime] (c : ℤ_[l]), c ≠ 0 → ∀ e : ℕ, 0 < e → ∃ N : ℕ, ∀ m : ℤ, PadicInt.toZModPow N c = (m : ZMod (l ^ N)) → ¬ ((l : ℤ) ^ N ∣ e * m) := by
  first | exact @GlobalTheory.padicInt_toZModPow_not_dvd_mul | exact GlobalTheory.padicInt_toZModPow_not_dvd_mul | (intros; apply GlobalTheory.padicInt_toZModPow_not_dvd_mul <;> assumption)
