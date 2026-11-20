import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalEqLowering
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicFlagUnipotentRadicalEqLowering.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_eq_lowering : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  first | exact @GlobalTheory.RadFullFlag.flagN_eq_lowers | exact GlobalTheory.RadFullFlag.flagN_eq_lowers | (intros; apply GlobalTheory.RadFullFlag.flagN_eq_lowers <;> assumption)
