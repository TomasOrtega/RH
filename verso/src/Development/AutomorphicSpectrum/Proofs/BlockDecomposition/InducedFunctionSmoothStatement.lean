import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionSmooth
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
Apply `GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FInducedFunctionSmooth.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.inducedFunction_smooth : ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev → GlobalTheory.CompanionTheory.ModelS.fRaw lam lev ∈ GlobalTheory.CompanionTheory.ModelS.SmF n := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | exact GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF | (intros; apply GlobalTheory.CompanionTheory.ModelS.fRaw_mem_SmF <;> assumption)
