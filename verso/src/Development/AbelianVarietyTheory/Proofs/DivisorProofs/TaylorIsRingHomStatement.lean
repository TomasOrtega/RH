import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorIsRingHom
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTaylorIsRingHom.lean&line=180#L180)
-/
theorem _root_.GlobalTheory.T.exists_ringHom_eq_taylor : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), ∃ T : A →+* MvPowerSeries (Fin n) B, ∀ f, T f = taylor ev (fun i => ⇑(ds i)) f := by
  first | exact @GlobalTheory.FormalOrigin.taylor_isRingHom | exact GlobalTheory.FormalOrigin.taylor_isRingHom | (intros; apply GlobalTheory.FormalOrigin.taylor_isRingHom <;> assumption)
