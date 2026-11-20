import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsPadicIntOfCompatibleZmodPow.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' : ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)), (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) → ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  first | exact @GlobalTheory.exists_padicInt_of_compatible_zmod_pow | exact GlobalTheory.exists_padicInt_of_compatible_zmod_pow | (intros; apply GlobalTheory.exists_padicInt_of_compatible_zmod_pow <;> assumption)
