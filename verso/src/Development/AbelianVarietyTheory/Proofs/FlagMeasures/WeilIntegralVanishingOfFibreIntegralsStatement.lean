import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FWeilIntegralVanishingOfFibreIntegrals.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.weil_integral_vanishing_of_fibre_integrals : WeilVanish := by
  first | exact @GlobalTheory.Dec.weilVanish | exact GlobalTheory.Dec.weilVanish | (intros; apply GlobalTheory.Dec.weilVanish <;> assumption)
