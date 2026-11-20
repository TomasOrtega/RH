import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTest
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FContinuousAutomorphicKernelDiscreteSeriesTest.lean&line=41#L41)
-/
theorem _root_.GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ), IsDSData B d → 1 ≤ B.I.n → LocDec B h → HBig B 32 h → Continuous (fun p : B.I.GA × B.I.GA => kern B.I (phe B d) p.1 p.2) := by
  first | exact @GlobalTheory.Dec.continuous_kern_phe | exact GlobalTheory.Dec.continuous_kern_phe | (intros; apply GlobalTheory.Dec.continuous_kern_phe <;> assumption)
