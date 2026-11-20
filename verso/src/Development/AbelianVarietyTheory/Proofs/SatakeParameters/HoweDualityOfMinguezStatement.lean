import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityOfMinguez
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoweBridge.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FHoweDualityOfMinguez.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.howe_duality_of_minguez : GlobalTheory.Published.MinguezThetaGL → GlobalTheory.Published.HoweDualityGL := by
  first | exact @GlobalTheory.HoweBridge.main | exact GlobalTheory.HoweBridge.main | (intros; apply GlobalTheory.HoweBridge.main <;> assumption)
