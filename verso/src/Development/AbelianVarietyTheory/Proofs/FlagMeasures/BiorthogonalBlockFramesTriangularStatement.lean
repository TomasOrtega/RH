import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RadCov.blockFrames_triangular` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBiorthogonalBlockFramesTriangular.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.biorthogonal_block_frames_triangular : ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ) (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ), Biorth r m T T' → Biorth r m U U' → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0) → (∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) → (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b, U' b * Y * U (b + c + 1) = (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  first | exact @GlobalTheory.RadCov.blockFrames_triangular | exact GlobalTheory.RadCov.blockFrames_triangular | (intros; apply GlobalTheory.RadCov.blockFrames_triangular <;> assumption)
