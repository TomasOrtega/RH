import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousUnitaryMultiplicativeEqArgPow.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) → ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) → (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) → ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  first | exact @GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | exact GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | (intros; apply GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow <;> assumption)
