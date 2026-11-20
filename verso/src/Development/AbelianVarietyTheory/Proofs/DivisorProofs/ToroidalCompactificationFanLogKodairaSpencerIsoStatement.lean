import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationFanLogKodairaSpencerIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TorKSField.toroidalForFanKS | exact GlobalTheory.TorKSField.toroidalForFanKS | (intros; apply GlobalTheory.TorKSField.toroidalForFanKS <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.toroidalCompactificationFan_logKodairaSpencer_iso : GlobalTheory.Published.ToroidalForFanKS := by
  first | exact @GlobalTheory.TorKSField.toroidalForFanKS | exact GlobalTheory.TorKSField.toroidalForFanKS | (intros; apply GlobalTheory.TorKSField.toroidalForFanKS <;> assumption)
