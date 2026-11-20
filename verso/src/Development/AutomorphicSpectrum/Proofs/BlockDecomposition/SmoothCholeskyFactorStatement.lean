import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCholeskyFactor
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeMeas
open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothCholeskyFactor.lean&line=198#L198)
-/
theorem _root_.GlobalTheory.T.smooth_positive_definite_sqrt : ∀ n : ℕ, ∃ σ₀ : Mat n → Mat n, ContDiffOn ℝ ∞ σ₀ {P | P.PosDef} ∧ ∀ P : Mat n, P.PosDef → σ₀ P * (σ₀ P)ᴴ = P := by
  first | exact @GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | exact GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section | (intros; apply GlobalTheory.CompanionTheory.ConeHaar.Chol.exists_smooth_section <;> assumption)
