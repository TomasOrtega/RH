import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FChevalleyUnits.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.chevalley_units : GlobalTheory.Published.ChevalleyUnits := by
  first | exact @GlobalTheory.Published.chevalleyUnits' | exact GlobalTheory.Published.chevalleyUnits' | (intros; apply GlobalTheory.Published.chevalleyUnits' <;> assumption)
