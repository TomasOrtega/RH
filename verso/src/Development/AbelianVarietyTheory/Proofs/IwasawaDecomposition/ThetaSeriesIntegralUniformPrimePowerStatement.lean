import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePower
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.serInt_outright` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FThetaSeriesIntegralUniformPrimePower.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  first | exact @GlobalTheory.serInt_outright | exact GlobalTheory.serInt_outright | (intros; apply GlobalTheory.serInt_outright <;> assumption)
