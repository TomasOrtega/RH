import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationEvaluationContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMollificationEvaluationContinuous.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.mollification_evaluation_continuous : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → ∀ z ∈ GLs n, ∃ L : Lp V 2 μ →L[ℝ] V, ∀ x : Lp V 2 μ, L x = Mol μ φ (⇑x) z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded | exact GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded | (intros; apply GlobalTheory.CompanionTheory.PresSobA.MolBounded.mol_bounded <;> assumption)
