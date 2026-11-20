import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsOrthonormalFrameOfIsotropicBlocks.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.exists_orthonormalFrame_of_isotropicBlocks : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ), n = n₀ + 2 * ∑ i, j i → (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → (∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0) → (∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → ∃ (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (s : Formalism.REAL.UJ ε₀) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ ∧ A₀ = B₀ * uMat s + ∑ k, B k * d k := by
  first | exact @GlobalTheory.FrameCompletion.exists_isFrame | exact GlobalTheory.FrameCompletion.exists_isFrame | (intros; apply GlobalTheory.FrameCompletion.exists_isFrame <;> assumption)
