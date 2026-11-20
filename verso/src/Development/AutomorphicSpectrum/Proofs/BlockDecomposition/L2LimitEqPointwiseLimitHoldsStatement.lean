import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2LimitEqPointwiseLimitHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FL2LimitEqPointwiseLimitHolds.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.l2_limit_eq_pointwise_limit_holds : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | exact GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit | (intros; apply GlobalTheory.CompanionTheory.PresSobA.l2_limit_eq_pointwise_limit <;> assumption)
