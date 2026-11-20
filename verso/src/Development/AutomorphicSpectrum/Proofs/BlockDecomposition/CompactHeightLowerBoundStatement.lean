import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactHeightLowerBound.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.compact_height_lower_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (D : Set (GAd σ J)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ g ∈ D, ∀ v : Fin n → E, v ≠ 0 → 1 ≤ P * hgt σ J g v := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_one_le_mul_hgt <;> assumption)
