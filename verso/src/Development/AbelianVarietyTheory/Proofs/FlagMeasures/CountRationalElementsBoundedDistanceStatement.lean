import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FCountRationalElementsBoundedDistance.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.count_rational_elements_bounded_distance : CountRat := by
  first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)
