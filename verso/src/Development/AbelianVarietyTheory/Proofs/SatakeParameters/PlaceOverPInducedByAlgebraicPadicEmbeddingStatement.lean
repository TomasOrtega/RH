import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DatumJets.Place.placeAbove` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPlaceOverPInducedByAlgebraicPadicEmbedding.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding : GlobalTheory.DatumJets.PlaceAbove := by
  first | exact @GlobalTheory.DatumJets.Place.placeAbove | exact GlobalTheory.DatumJets.Place.placeAbove | (intros; apply GlobalTheory.DatumJets.Place.placeAbove <;> assumption)
