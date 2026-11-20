import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsKFiniteSubmoduleContaining.lean&line=164#L164)
-/
theorem _root_.GlobalTheory.T.exists_k_finite_submodule_containing : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 → (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) → ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin | exact GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin | (intros; apply GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin <;> assumption)
