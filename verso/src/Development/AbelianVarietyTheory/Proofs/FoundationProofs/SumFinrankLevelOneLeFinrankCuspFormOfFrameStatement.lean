import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSumFinrankLevelOneLeFinrankCuspFormOfFrame.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (CuspForm Γ k) → (∀ j, IsCF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | exact GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | (intros; apply GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm <;> assumption)
