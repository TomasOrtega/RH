import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHighestWeightMemCone.lean&line=136#L136)
-/
theorem _root_.GlobalTheory.T.highest_weight_mem_cone : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev → ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V), Formalism.REAL.KHighest (fun _ => true) K ν x → (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) → (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) → (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) → inCone lev (ν - μ) := by
  first | exact @GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest | exact GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest | (intros; apply GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest <;> assumption)
