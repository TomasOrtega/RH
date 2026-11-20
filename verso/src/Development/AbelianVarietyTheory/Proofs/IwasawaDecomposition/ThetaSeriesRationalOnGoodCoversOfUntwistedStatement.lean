import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesRationalOnGoodCoversOfUntwisted
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FThetaSeriesRationalOnGoodCoversOfUntwisted.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted : GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.UntwRatS → GlobalTheory.SerStd.SeriesRatS := by
  first | exact @GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | exact GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS | (intros; apply GlobalTheory.SerStdTwist.seriesRatS_of_untwRatS <;> assumption)
