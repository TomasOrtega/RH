import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FFiniteDimensionalOfGammaLe.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | exact GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | (intros; apply GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le <;> assumption)
