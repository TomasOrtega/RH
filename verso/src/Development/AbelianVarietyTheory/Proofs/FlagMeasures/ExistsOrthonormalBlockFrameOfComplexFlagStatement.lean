import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RadCov.exists_orthonormal_block_frame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsOrthonormalBlockFrameOfComplexFlag.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.exists_orthonormal_block_frame_of_complex_flag : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ → (∀ b, m ≤ b → W b = ⊤) → (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) → ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧ ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  first | exact @GlobalTheory.RadCov.exists_orthonormal_block_frame | exact GlobalTheory.RadCov.exists_orthonormal_block_frame | (intros; apply GlobalTheory.RadCov.exists_orthonormal_block_frame <;> assumption)
