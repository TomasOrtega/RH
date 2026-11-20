import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ApproximateIdentityExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FApproximateIdentityExists.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.approximate_identity_exists : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure], ∃ φ : ℕ → Mat n → ℝ, (∀ k, IsTest (φ k)) ∧ (∀ k y, 0 ≤ φ k y) ∧ (∀ k, ∫ y : G n, φ k y.val ∂μ = 1) ∧ ∀ N ∈ 𝓝 (1 : G n), ∀ᶠ k in atTop, ∀ y : G n, φ k y.val ≠ 0 → y ∈ N := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | exact GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers | (intros; apply GlobalTheory.CompanionTheory.PresSobA.exists_mollifiers <;> assumption)
