import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieAlgebraOfTangentCurve
import Formalism.UnipotentAdelicQuotients.SmComplete
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLieAlgebraOfTangentCurve.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.lie_algebra_of_tangent_curve : ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsClosedMatrixGroup G → ∀ (γ : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), γ 0 = 1 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ G) → HasDerivAt γ Y 0 → Y ∈ lieAlg G := by
  first | exact @GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | exact GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg | (intros; apply GlobalTheory.CompanionTheory.SmTangent.tangent_mem_lieAlg <;> assumption)
