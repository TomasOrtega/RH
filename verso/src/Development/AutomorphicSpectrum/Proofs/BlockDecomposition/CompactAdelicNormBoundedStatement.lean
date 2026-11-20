import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.RedCov.Simple
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCompactAdelicNormBounded.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.compact_adelic_norm_bounded : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (D : Set (Fin N → AF F)), IsCompact D → ∃ P : ℝ, 0 < P ∧ ∀ y ∈ D, GroundTheory.Automorphic.Reduction.adelicNorm y ≤ P := by
  first | exact @GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | exact GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact | (intros; apply GlobalTheory.CompanionTheory.RedCov.Simple.exists_adelicNorm_le_of_isCompact <;> assumption)
