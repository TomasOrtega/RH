import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FConvolutionSmoothL2.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.convolutionSmoothL2_of_def : ConvolutionSmoothL2 := by
  first | exact @GlobalTheory.SmoothGrowth.convolutionSmoothL2 | exact GlobalTheory.SmoothGrowth.convolutionSmoothL2 | (intros; apply GlobalTheory.SmoothGrowth.convolutionSmoothL2 <;> assumption)
