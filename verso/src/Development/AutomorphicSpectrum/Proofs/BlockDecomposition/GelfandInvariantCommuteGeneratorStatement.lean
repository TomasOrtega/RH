import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteGenerator
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGelfandInvariantCommuteGenerator.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.gelfand_invariant_commute_generator : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel E → ∀ (m : ℕ) (a b : Fin n), gelA E m * E a b = E a b * gelA E m := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.gelA_central | exact GlobalTheory.CompanionTheory.ModelS.gelA_central | (intros; apply GlobalTheory.CompanionTheory.ModelS.gelA_central <;> assumption)
