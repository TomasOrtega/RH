import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFinite
import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabUpTo
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FBoundedIntegralMatricesFinite.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.bounded_integral_matrices_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | exact GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | (intros; apply GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite <;> assumption)
