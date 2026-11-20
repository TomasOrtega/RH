import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrablePh
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.KernelExpansion.kernelB | exact GlobalTheory.KernelExpansion.kernelB | (intros; apply GlobalTheory.KernelExpansion.kernelB <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kernelB' : KernelB := by
  first | exact @GlobalTheory.KernelExpansion.kernelB | exact GlobalTheory.KernelExpansion.kernelB | (intros; apply GlobalTheory.KernelExpansion.kernelB <;> assumption)
