import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnitaryGroup
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
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsHaarUnitaryGroup.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_haar_unitary_group : ∀ (n : ℕ) [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)] [BorelSpace (Matrix.unitaryGroup (Fin n) ℂ)], ∃ κ : Measure (Matrix.unitaryGroup (Fin n) ℂ), IsFiniteMeasure κ ∧ κ.IsMulRightInvariant ∧ κ.IsOpenPosMeasure := by
  first | exact @GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | exact GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup | (intros; apply GlobalTheory.CompanionTheory.ModelS.exists_rightInvariant_measure_unitaryGroup <;> assumption)
