import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzLinearChange
import Mathlib
open scoped Matrix SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSchwartzLinearChange.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.schwartz_linear_change : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  first | exact @GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | exact GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | (intros; apply GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul <;> assumption)
