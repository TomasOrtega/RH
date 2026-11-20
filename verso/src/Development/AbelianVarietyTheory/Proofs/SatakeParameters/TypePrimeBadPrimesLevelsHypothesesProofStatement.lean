import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProof
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FTypePrimeBadPrimesLevelsHypothesesProof.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses : GlobalTheory.DatumJets.TypePrimeBadPrimesLevelsHypotheses := by
  first | exact @GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | exact GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof | (intros; apply GlobalTheory.DatumJets.HidaSetting.typePrimeBadPrimesLevelsHypotheses_proof <;> assumption)
