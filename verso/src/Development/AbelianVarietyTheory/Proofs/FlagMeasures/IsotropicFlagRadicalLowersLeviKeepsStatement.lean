import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagRadicalLowersLeviKeeps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IwConst.FlagMem.lowers_keeps` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsotropicFlagRadicalLowersLeviKeeps.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.isotropicFlag_radical_lowers_levi_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∀ u ∈ flagN ε W, uMat u - 1 ∈ lowers ε W) ∧ ∀ m ∈ flagM ε W, uMat m ∈ keeps ε W ∧ (uMat m)ᴴ ∈ keeps ε W := by
  first | exact @GlobalTheory.IwConst.FlagMem.lowers_keeps | exact GlobalTheory.IwConst.FlagMem.lowers_keeps | (intros; apply GlobalTheory.IwConst.FlagMem.lowers_keeps <;> assumption)
