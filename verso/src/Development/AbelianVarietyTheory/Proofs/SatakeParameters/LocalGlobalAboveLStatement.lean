import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLocalGlobalAboveL.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.local_global_above_l : GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.LocalLanglandsGL → GlobalTheory.Published.CaraianiLocalGlobal → GlobalTheory.Published.LocalGlobalAboveL := by
  first | exact @GlobalTheory.CaraianiAboveL.main | exact GlobalTheory.CaraianiAboveL.main | (intros; apply GlobalTheory.CaraianiAboveL.main <;> assumption)
