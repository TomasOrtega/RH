import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnipotentUpperInvUpperTriangularBounded
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.unipotent_upper_inv_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FUnipotentUpperInvUpperTriangularBounded.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.unipotent_upper_inv_upperTriangular_bounded : ∀ (N : ℕ) (C : ℝ), ∃ C' : ℝ, ∀ n : Matrix (Fin N) (Fin N) ℝ, (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → (∀ i j, |n i j| ≤ C) → ∃ m : Matrix (Fin N) (Fin N) ℝ, m * n = 1 ∧ n * m = 1 ∧ (∀ i j, j < i → m i j = 0) ∧ ∀ i j, |m i j| ≤ C' := by
  first | exact @GlobalTheory.unipotent_upper_inv_bounded | exact GlobalTheory.unipotent_upper_inv_bounded | (intros; apply GlobalTheory.unipotent_upper_inv_bounded <;> assumption)
