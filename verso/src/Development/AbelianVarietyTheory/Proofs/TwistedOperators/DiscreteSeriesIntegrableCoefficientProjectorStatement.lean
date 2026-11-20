import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjector
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FDiscreteSeriesIntegrableCoefficientProjector.lean&line=282#L282)
-/
theorem _root_.GlobalTheory.T.discreteSeries_integrableCoefficient_projector : ∀ X : ProvA, DiscreteSeriesPositivity X → CoverHaarIntegration X → DiscreteSeriesHighestVector X := by
  first | exact @GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | exact GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity | (intros; apply GlobalTheory.DSProj.discreteSeriesHighestVector_of_positivity <;> assumption)
