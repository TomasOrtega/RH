import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlock
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LeviIso.Range.mem_flagM_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FMemIsotropicFlagSelfAdjointLeviIffBlock.lean&line=185#L185)
-/
theorem _root_.GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ m : Formalism.REAL.UJ ε, m ∈ flagM ε W ↔ ∃ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Formalism.REAL.UJ ε₀), (∀ i, (x i).det ≠ 0) ∧ uMat m = lev ε B B₀ x (uMat g) := by
  first | exact @GlobalTheory.LeviIso.Range.mem_flagM_iff | exact GlobalTheory.LeviIso.Range.mem_flagM_iff | (intros; apply GlobalTheory.LeviIso.Range.mem_flagM_iff <;> assumption)
