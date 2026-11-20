import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLimitRightDerivatives
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RwAppend
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUniformLimitRightDerivatives.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.uniform_limit_right_derivatives : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (g : ℕ → Mat n → V), (∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) → (∀ w, UniformCauchySeqOn (fun k => Rw w (g k)) atTop (GLs n)) → ∃ Gf : List (Bool × Fin n × Fin n) → Mat n → V, (∀ w, TendstoUniformlyOn (fun k => Rw w (g k)) (Gf w) atTop (GLs n)) ∧ ContDiffOn ℝ ∞ (Gf []) (GLs n) ∧ ∀ w, ∀ z ∈ GLs n, Rw w (Gf []) z = Gf w z := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | exact GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth | (intros; apply GlobalTheory.CompanionTheory.PresSobA.LimSmooth.limit_smooth <;> assumption)
