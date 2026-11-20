import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorKSField.toroidalForFanKS` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FToroidalCompactificationFanLogKodairaSpencerIso.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso : GlobalTheory.Published.ToroidalForFanKS := by
  first | exact @GlobalTheory.TorKSField.toroidalForFanKS | exact GlobalTheory.TorKSField.toroidalForFanKS | (intros; apply GlobalTheory.TorKSField.toroidalForFanKS <;> assumption)
