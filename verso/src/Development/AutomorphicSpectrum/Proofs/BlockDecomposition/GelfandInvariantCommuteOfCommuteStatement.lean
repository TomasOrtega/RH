import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute
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
Apply `GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGelfandInvariantCommuteOfCommute.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.gelfand_invariant_commute_of_commute : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V), (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units | exact GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units <;> assumption)
