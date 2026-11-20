import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousAlgebraNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GTil
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousAlgebraNorm.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.continuous_algebra_norm : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (Algebra.norm F : E → F) := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.continuous_norm_quadExt | exact GlobalTheory.CompanionTheory.GaussLam.continuous_norm_quadExt | (intros; apply GlobalTheory.CompanionTheory.GaussLam.continuous_norm_quadExt <;> assumption)
