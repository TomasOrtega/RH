import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsJointEigenvectorNonzero

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsJointEigenvectorNonzero.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_joint_eigenvector_nonzero : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ι J : Type) [Fintype J] (H : ι → Module.End ℂ W), (∀ i i', Commute (H i) (H i')) → ∀ (c : J → ℂ) (s : J → ι) (v : W) (m : ℕ), Module.finrank ℂ W ≤ m → ((∑ j, c j • H (s j)) ^ m) v ≠ 0 → ∃ v₀ : W, v₀ ≠ 0 ∧ ∃ χ : ι → ℂ, (∀ i, H i v₀ = χ i • v₀) ∧ ∑ j, c j * χ (s j) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | exact GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero | (intros; apply GlobalTheory.CompanionTheory.LinAlg.exists_joint_eigenvector_combination_ne_zero <;> assumption)
