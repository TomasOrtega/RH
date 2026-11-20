import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesStepBoundOfCountingHypotheses
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.stepBoundAt_of_countHyp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FDiscreteSeriesStepBoundOfCountingHypotheses.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.discreteSeries_stepBound_of_countingHypotheses : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → ∀ P : ℕ, GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis.StepBoundAt B b P := by
  first | exact @GlobalTheory.Dec.stepBoundAt_of_countHyp | exact GlobalTheory.Dec.stepBoundAt_of_countHyp | (intros; apply GlobalTheory.Dec.stepBoundAt_of_countHyp <;> assumption)
