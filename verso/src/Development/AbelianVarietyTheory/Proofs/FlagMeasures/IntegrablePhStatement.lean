import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KernelExpansion.kernelB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIntegrablePh.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.kernelB' : KernelB := by
  first | exact @GlobalTheory.KernelExpansion.kernelB | exact GlobalTheory.KernelExpansion.kernelB | (intros; apply GlobalTheory.KernelExpansion.kernelB <;> assumption)
