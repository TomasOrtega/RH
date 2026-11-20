import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountRationalElementsBoundedDistance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.count_rational_elements_bounded_distance : CountRat := by
  first | exact @GlobalTheory.Dec.BoundedDistance.countRat | exact GlobalTheory.Dec.BoundedDistance.countRat | (intros; apply GlobalTheory.Dec.BoundedDistance.countRat <;> assumption)
