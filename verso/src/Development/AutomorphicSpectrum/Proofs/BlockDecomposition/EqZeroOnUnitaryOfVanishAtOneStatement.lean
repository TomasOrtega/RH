import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOne
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
Apply `GlobalTheory.CompanionTheory.ModelS.Sep.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FEqZeroOnUnitaryOfVanishAtOne.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S → (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) → ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.Sep.main | exact GlobalTheory.CompanionTheory.ModelS.Sep.main | (intros; apply GlobalTheory.CompanionTheory.ModelS.Sep.main <;> assumption)
