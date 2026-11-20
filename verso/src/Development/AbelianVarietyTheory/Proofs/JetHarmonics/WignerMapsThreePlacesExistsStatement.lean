import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.AmapsShExists
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FWignerMapsThreePlacesExists.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.wignerMapsThreePlaces_exists : GlobalTheory.WigSh.AmapsShExists := by
  first | exact @GlobalTheory.WigSh.amapsShExists | exact GlobalTheory.WigSh.amapsShExists | (intros; apply GlobalTheory.WigSh.amapsShExists <;> assumption)
