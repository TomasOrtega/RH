import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZero
import Mathlib
open NumberField Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_normOne_det_one_add_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsNormOneCmFieldDetOneAddNeZero.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_normOne_det_one_add_ne_zero | exact GlobalTheory.exists_normOne_det_one_add_ne_zero | (intros; apply GlobalTheory.exists_normOne_det_one_add_ne_zero <;> assumption)
