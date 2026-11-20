import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroOfRowsSeparating
import Mathlib
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_det_ne_zero_of_rows_separating` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDetNeZeroOfRowsSeparating.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_det_ne_zero_of_separating_functionals : ∀ (K : Type) [Field K] (σ : Type) (h : ℕ) (M : σ → Fin h → K), (∀ a : Fin h → K, (∀ s, ∑ j, a j * M s j = 0) → a = 0) → ∃ s : Fin h → σ, (Matrix.of fun i j => M (s i) j).det ≠ 0 := by
  first | exact @GlobalTheory.exists_det_ne_zero_of_rows_separating | exact GlobalTheory.exists_det_ne_zero_of_rows_separating | (intros; apply GlobalTheory.exists_det_ne_zero_of_rows_separating <;> assumption)
